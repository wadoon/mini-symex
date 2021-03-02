import BinaryExpr.Operator.EQUAL
import BinaryExpr.Operator.NOT_EQUAL
import UnaryExpr.Operator.NEGATE
import java.util.concurrent.atomic.AtomicInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
var PRINT_ATTRIBUTES = true

class State(
    var uniqueCounter: AtomicInteger = AtomicInteger(0),
    val signature: HashMap<Variable, TypeDecl> = HashMap(),
    val variables: HashMap<Variable, MutableList<Int>> = HashMap(),
    val assumptions: MutableList<String> = ArrayList(),
    val assertions: MutableList<String> = ArrayList()
) {
    fun freshConst(lhs: Variable): String {
        val v = variables.computeIfAbsent(lhs) { arrayListOf(uniqueCounter.getAndIncrement()) }
        v.add(uniqueCounter.getAndIncrement())
        return currentVar(lhs)
    }

    fun dischargeIntoSmt() {
        fun join(seq: List<String>, fn: (String) -> String): String {
            return if (seq.isEmpty()) "true"
            else seq.joinToString("\n", transform = fn)
        }

        val assert = join(assertions) { "    (not $it)" }
        val assume = join(assumptions) { "    $it" }
        val sb = StringBuilder()
        sb.append(";; goal\n")
        sb.append(printSignature())
        sb.append("\n\n(assert (and\n")
        sb.append(";;; assumptions\n").append(assume).append("\n\n")
        sb.append(";;; assertions\n").append(assert).append("\n")
        sb.append("))\n(check-sat)\n;;--end of goal\n")
        print(sb)
    }

    private fun printSignature(): String {
        val sb = StringBuilder()
        variables.forEach { (t, u) ->
            val type = signature[t] ?: error("variable $t is not declared")
            require(!type.array) { "arrays currently not supported" }
            u.joinTo(sb, "") { i ->
                "(declare-const ${t.id}_${i} ${type.toSmtType()})\n"
            }
        }
        return sb.toString()
    }

    fun newGoal(): State = State(
        uniqueCounter = uniqueCounter,
        signature = HashMap(signature),
        variables = HashMap(variables),
        assumptions = ArrayList(assumptions),
        assertions = arrayListOf() //delete assertions
    )

    fun currentVar(id: Variable): String {
        val cnt = variables.computeIfAbsent(id) { arrayListOf(uniqueCounter.getAndIncrement()) }.last()
        return "${id.id}_${cnt}"
    }
}

class SymEx {
    val dischargedGoals = arrayListOf<State>()

    fun encodeExpression(expr: Expr, state: State): String = when (expr) {
        is BinaryExpr ->
            if (expr.op == NOT_EQUAL)
                encodeExpression(UnaryExpr(NEGATE, expr.copy(op = EQUAL)), state)
            else
                "(${expr.op.smtSymbol} ${encodeExpression(expr.left, state)} ${
                    encodeExpression(
                        expr.right,
                        state
                    )
                })"
        is FunctionCall -> TODO()
        is IntLit -> expr.value.toString()
        is UnaryExpr -> "(${expr.op.smtSymbol} ${encodeExpression(expr.right, state)})"
        is Variable -> state.currentVar(expr)
        is BoolLit -> expr.value.toString()
        is QuantifiedExpr -> {
            val q = expr.quantifier.smtSymbol
            val b = expr.binders.joinToString(" ") { (t, v) ->
                "(${t.toSmtType()} ${v.id})"
            }
            "($q ($b))"
        }
    }

    fun executeStatement(s: Statement, state: State): State {
        return when (s) {
            is AssertStmt -> {
                val e = encodeExpression(s.cond, state)
                    .named("assertion at offset ${s.position?.startOffset}")
                val g = state.newGoal()
                state.assertions += e
                discharge(state)
                g.assumptions += e
                g
            }
            is AssumeStmt -> {
                val e = encodeExpression(s.cond, state)
                state.assumptions += e
                state
            }
            is AssignStmt -> {
                require(s.arrayAccess == null) { "arrays currently unsupported" }
                s.decl?.let {
                    state.signature[s.id] = it
                }
                val lhs = s.id
                val rhs = encodeExpression(s.lhs, state)
                val fresh = state.freshConst(lhs)
                state.assumptions += ("(= $fresh $rhs)")
                state
            }
            is Body -> s.statements.fold(state) { acc, statement -> executeStatement(statement, acc) }
            is EmptyStmt -> {
                state
            }
            is HavocStmt -> {
                s.ids.forEach {
                    state.freshConst(it) //just create new constants
                }
                state
            }
            is IfStmt -> {
                //evaluate condition in the current goal
                val cond = encodeExpression(s.cond, state)
                val notCond = "(not $cond)"

                // we split the goal into three subgoals:
                val thenGoal = state.newGoal()   // (1) subgoal of the then-branch
                val elseGoal = state.newGoal()   // (2) subgoal of the else-branch
                val afterIf = state.newGoal()    // (3) subgoal after if-branch

                // assume that the guard holds in the then-branch
                thenGoal.assumptions += cond

                // assume that the guard does not hold in the then-branch
                elseGoal.assumptions += notCond

                //execute both branches
                val finalThenGoal = executeStatement(s.then, thenGoal)
                val finalElseGoal = executeStatement(s.otherwise, elseGoal)

                mergeInto(
                    cond to finalThenGoal,
                    notCond to finalElseGoal, afterIf
                )
                afterIf
            }
            is WhileStmt -> {
                val init = state.newGoal()
                val preservation = state.newGoal()
                val termination = state.newGoal()

                init.assertions += encodeExpression(s.loopInv, state)
                discharge(init)

                preservation.assumptions.clear()
                preservation.assertions.clear()
                s.erase.forEach { preservation.freshConst(it) }
                preservation.assumptions += encodeExpression(s.loopInv, preservation)
                preservation.assumptions += encodeExpression(s.cond, preservation)
                val afterBody = executeStatement(s.then, preservation)
                afterBody.assertions += encodeExpression(s.loopInv, afterBody)
                discharge(afterBody)

                termination.assumptions.clear()
                termination.assertions.clear()
                s.erase.forEach { termination.freshConst(it) }
                termination.assumptions += encodeExpression(s.loopInv, preservation)
                termination.assumptions += "(not ${encodeExpression(s.cond, preservation)})"

                termination
            }
        }
    }

    private fun mergeInto(
        firstBranch: Pair<String, State>,
        secondBranch: Pair<String, State>,
        target: State
    ) {
        fun conditionallyAdd(target: MutableList<String>, source: MutableList<String>, cond: String) {
            target.addAll(source.map { "(=> $cond $it)" })
        }

        conditionallyAdd(target.assumptions, firstBranch.second.assumptions, firstBranch.first)
        conditionallyAdd(target.assumptions, secondBranch.second.assumptions, secondBranch.first)

        val allVars = secondBranch.second.signature.keys + firstBranch.second.signature.keys
        allVars.forEach { v ->
            val vThen = firstBranch.second.currentVar(v)
            val vElse = secondBranch.second.currentVar(v)
            if (vThen != vElse) {//we have to merge
                val newValue = target.freshConst(v)
                target.assumptions += "(= $newValue (ite ${firstBranch.first} $vThen $vElse))"
            }
        }
    }

    private fun discharge(state: State) {
        state.dischargeIntoSmt()
        dischargedGoals += state
    }
}

private fun String.named(s: String): String = if (PRINT_ATTRIBUTES) "(! $this :named \"$s\")" else this
private fun TypeDecl.toSmtType(): String = toType().toSmtType()
private fun Type.toSmtType(): String = name.capitalize()