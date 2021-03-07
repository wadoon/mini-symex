import BinaryExpr.Operator.EQUAL
import BinaryExpr.Operator.NOT_EQUAL
import UnaryExpr.Operator.NEGATE
import java.io.PrintWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
var PRINT_ATTRIBUTES = true

class SymEx2(val procedures: List<Procedure> = arrayListOf()) {
    inner class Scope(
        val signature: HashMap<Variable, TypeDecl> = HashMap(),
        val variables: HashMap<Variable, MutableList<Int>> = HashMap()
    ) {
        fun sub() = Scope(
            signature = HashMap(signature),
            variables = variables
        )

        fun clone() = Scope(signature = HashMap(signature), variables = HashMap(variables))

        fun currentVar(id: Variable): String {
            val cnt = variables.computeIfAbsent(id) { arrayListOf(0) }.last()
            return "${id.id}_${cnt}"
        }

        fun freshConst(id: Variable): String {
            val cnt = variables.computeIfAbsent(id) { arrayListOf(0) }
            val fresh = cnt.last() + 1
            cnt.add(fresh)

            val t = signature[id] ?: error("Variable $id not declared")
            declareConst(t.toType(), id, fresh)
            return currentVar(id)
        }
    }

    private val vcgGenerated = HashSet<String>()

    val commands = arrayListOf<String>()

    private fun declareConst(t: Type, v: Variable, i: Int) {
        if (t.dimension == 0)
            commands += "(declare-const ${v.id}_${i} ${t.toSmtType()})\n"
        else
            commands += "(declare-const ${v.id}_${i} (Array Int ${t.toSmtType()}))\n"
        require(t.dimension < 2)
    }

    private fun discharge(expr: String, name: String = "") {
        isolatedGoal(name) {
            assert(expr)
            checkSat()
        }
    }

    private fun checkSat() {
        commands += "(check-sat)"
    }

    private fun assume(expr: String, name: String = "") {
        if (name.isNotEmpty())
            commands += "(echo \"$name\")"
        commands += "(assert $expr)"
    }

    private fun assert(expr: String) = assume("(not $expr)")

    private fun <T> sideGoal(name: String = "", fn: () -> T): T {
        commands += ";;; -- $name --------------------------------"
        commands += "(echo \"$name\")"
        return fn()
    }

    private fun <T> isolatedGoal(name: String = "", fn: () -> T): T {
        //commands += ";;; -- $name --------------------------------"
        commands += "(push 1)"
        commands += "(echo \"$name\")"
        val scope = fn()
        commands += "(pop 1)"
        return scope
    }

    fun encodeExpression(expr: Expr, state: Scope): String = encodeExpression(expr, state::currentVar)

    fun encodeExpression(expr: Expr, state: (Variable) -> String): String = when (expr) {
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
        is FunctionCall -> error("Function calls only supported as standalone rhs.")
        is IntLit -> expr.value.toString()
        is UnaryExpr -> "(${expr.op.smtSymbol} ${encodeExpression(expr.right, state)})"
        is Variable -> state(expr)
        is BoolLit -> expr.value.toString()
        is QuantifiedExpr -> {
            val q = expr.quantifier.smtSymbol
            val b = expr.binders.joinToString(" ") { (t, v) ->
                "(${t.toSmtType()} ${v.id})"
            }
            val s = { a: Variable ->
                if (expr.binders.any { (_, v) -> a == v }) a.id
                else state(a)
            }
            "($q ($b) ${encodeExpression(expr.sub, s)})"
        }
        is ArrayAccess -> {
            expr.args.foldRight(encodeExpression(expr.id, state)) { e, acc ->
                "(select $acc ${encodeExpression(e, state)})"
            }
        }
    }


    fun executeStatement(s: Statement, state: Scope = Scope()): Scope {
        return when (s) {
            is AssertStmt -> {
                val e = encodeExpression(s.cond, state)
                    .named(s.named)
                    .position(s.position)
                val desc = s.description ?: "assert '${s.cond.toHuman()}' @ ${s.position}"
                discharge(e, name = desc)
                assume(e)
                state
            }
            is AssumeStmt -> {
                val desc = s.description ?: "assume '${s.cond.toHuman()}' @ ${s.position}"
                val e = encodeExpression(s.cond, state)
                assume(e, desc)
                state
            }
            is AssignStmt -> {
                s.decl?.let { state.signature[s.id] = it }

                s.rhs?.let { expr ->
                    val lhs = s.id
                    val rhs =
                        if (expr is FunctionCall)
                            encodeFunctionCallExpression(expr, state)
                        else
                            encodeExpression(expr, state)

                    val value = s.arrayAccess?.let {
                        val aexpr = encodeExpression(it, state)
                        "(store ${state.currentVar(s.id)} $aexpr $rhs)"
                    } ?: rhs

                    val fresh = state.freshConst(lhs)
                    assume("(= $fresh $value)")
                }
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
                val thenGoal = state.sub()   // (1) new scopes of the then-branch
                val elseGoal = state.sub()   // (2) new scopes of the else-branch
                val afterIf = state.sub()    // (3) new scopes after if-branch

                // assume that the guard holds in the then-branch
                val finalThenGoal = sideGoal {
                    assume(cond)
                    executeStatement(s.then, thenGoal)
                }

                // assume that the guard does not hold in the then-branch
                val finalElseGoal = sideGoal {
                    assume(notCond)
                    executeStatement(s.otherwise, elseGoal)
                }

                val allVars = finalThenGoal.signature.keys + finalElseGoal.signature.keys
                allVars.forEach { v ->
                    val vThen = finalThenGoal.currentVar(v)
                    val vElse = finalElseGoal.currentVar(v)
                    if (vThen != vElse) {// Conflict found: We have to merge
                        val newValue = afterIf.freshConst(v)
                        assume("(= $newValue (ite $cond $vThen $vElse))")
                    }
                }

                afterIf
            }
            is WhileStmt -> {
                isolatedGoal {
                    val init = state.sub()
                    val loopInv = encodeExpression(s.loopInv, init)
                    discharge(loopInv, "Loop Invariant Initially Holds")
                    init
                }

                isolatedGoal {
                    val preservation = state.sub()
                    s.erase.forEach { preservation.freshConst(it) }
                    assume(encodeExpression(s.loopInv, preservation))
                    assume(encodeExpression(s.cond, preservation))
                    val afterBody = executeStatement(s.then, preservation)
                    discharge(
                        encodeExpression(s.loopInv, afterBody),
                        "Ensure Preservation of Loop Invariant"
                    )
                    afterBody
                }

                // no side goal, we want to presume that the invariant and the violated condition.
                val termination = state.sub()
                s.erase.forEach { termination.freshConst(it) }
                assume(encodeExpression(s.loopInv, termination))
                val cond = encodeExpression(s.cond, termination)
                assume("(not $cond)")
                termination
            }
        }
    }


    private fun encodeFunctionCallExpression(expr: FunctionCall, state: Scope): String {
        val function = procedures.find { it.name == expr.id.id }
        require(function != null)

        // Prove the function behind the function call
        if (function.name !in vcgGenerated)
            proveBody(function)

        // reduce the arguments to single variables (introduce assignments)
        isolatedGoal {
            val sig = state.clone()

            val params: List<String> = function.args.map { (t, v) ->
                sig.signature[v] = t
                sig.freshConst(v)
            }

            expr.args.zip(params).forEach { (e, p) ->
                assume("(= $p ${encodeExpression(e, state)})")
            }

            // discharge the precondition
            assert(encodeExpression(function.requires, sig))
            checkSat()
        }

        if (function.returnType.toType() != Type.VOID) {
            val variable = Variable("__retValue__")
            state.signature[variable] = function.returnType
            val retValue = state.freshConst(variable)
            assume(
                "(= $retValue ${encodeExpression(function.ensures, state)})",
                name = "Post-condition of ${function.name}"
            )
            return retValue
        }
        return ""
    }

    fun proveBody(function: Procedure) {
        val proofObligation = Body(arrayListOf())
        proofObligation.statements.add(AssumeStmt(function.requires, "pre-condition of ${function.name}"))
        proofObligation.statements.add(function.body)
        proofObligation.statements.add(AssertStmt(function.ensures, "post-condition of ${function.name}"))
        executeStatement(proofObligation)
    }

    fun encodeInto(out: PrintWriter) {
        commands.forEach { out.println(it) }
    }
}

private fun String.named(s: String?): String = if (PRINT_ATTRIBUTES && s != null) "(! $this :named \"$s\")" else this
private fun String.position(p: Position?): String =
    if (PRINT_ATTRIBUTES && p != null) "(! $this :source-file \"${p.source}\" :start ${p.startOffset} :end ${p.endOffset})" else this


private fun TypeDecl.toSmtType(): String = toType().toSmtType()
private fun Type.toSmtType(): String = name.capitalize()