import java.util.concurrent.atomic.AtomicInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */

class Goal(
    var uniqueCounter: AtomicInteger = AtomicInteger(0),
    val signature: HashMap<Variable, Type> = HashMap(),
    val variables: HashMap<Variable, Int> = HashMap(),
    val assumptions: MutableList<String> = ArrayList<String>(),
    val assertions: MutableList<String> = ArrayList<String>()
) {
    fun freshConst(lhs: Variable): String {
        variables[lhs] = variables.getOrDefault(lhs, 0) + uniqueCounter.getAndIncrement()
        return currentVar(lhs)
    }

    fun dischargeIntoSmt() {
        fun join(seq: List<String>, prefix: String = ""): String {
            return if (seq.isEmpty()) "true"
            else seq.joinToString("\n") { prefix + it }
        }

        val assert = join(assertions, "    ")
        val assume = join(assumptions, "    ")
        val sb = StringBuilder()
        sb.append(";; goal\n")
        sb.append(printSignature())
        sb.append("\n\n(assert (=>\n")
        sb.append(";;; assumptions\n")
        sb.append("(and \n").append(assume).append(")\n\n")
        sb.append(";;; assertions\n")
        sb.append("(and \n").append(assert).append(")\n\n")
        sb.append(assert)
            .append("))\n;;--end of goal\n")
        print(sb)
    }

    private fun printSignature(): String {
        val sb = StringBuilder()
        variables.forEach { (t, u) ->
            val type = signature[t] ?: error("variable $t is not declared")
            require(!type.array) { "arrays currently not supported" }
            (0..u).joinTo(sb, "") { i ->
                "(declare-const ${t.id}_${i} ${type.name.capitalize()})\n"
            }
        }
        return sb.toString()
    }

    fun newGoal(): Goal {
        val g = Goal(
            uniqueCounter = uniqueCounter,
            signature = HashMap(signature),
            variables = HashMap(variables),
            assumptions = ArrayList(assumptions),
            assertions = ArrayList(assertions)
        )
        return g
    }

    fun currentVar(id: Variable): String {
        val cnt = variables.getOrPut(id) { 0 }
        return "${id.id}_${cnt}"
    }
}

class SymEx {
    val dischargedGoals = arrayListOf<Goal>()
    fun operator(s: String): String = when (s) {
        "==" -> "="
        else -> s
    }

    fun encodeExpression(expr: Expr, goal: Goal): String {
        return when (expr) {
            is BinaryExpr -> "(${operator(expr.op)} ${encodeExpression(expr.left, goal)} ${
                encodeExpression(
                    expr.right,
                    goal
                )
            })"
            is FunctionCall -> TODO()
            is IntLit -> expr.value.toString()
            is UnaryExpr -> "(${operator(expr.op)} ${encodeExpression(expr.right, goal)})"
            is Variable -> goal.currentVar(expr)
            is BoolLit -> expr.value.toString()
        }
    }

    fun executeStatement(s: Statement, goal: Goal): Goal {
        return when (s) {
            is AssertStmt -> {
                val e = encodeExpression(s.cond, goal)
                val g = goal.newGoal()
                goal.assertions += "(not $e)"
                discharge(goal)
                g.assumptions += e
                g
            }
            is AssumeStmt -> {
                val e = encodeExpression(s.cond, goal)
                goal.assumptions += e
                goal
            }
            is AssignStmt -> {
                require(s.arrayAccess == null) { "arrays currently unsupported" }
                s.decl?.let {
                    goal.signature[s.id] = it
                }
                val lhs = s.id
                val rhs = encodeExpression(s.lhs, goal)
                val fresh = goal.freshConst(lhs)
                goal.assertions += ("(= $fresh $rhs)")
                goal
            }
            is Body -> s.statements.fold(goal) { acc, statement -> executeStatement(statement, acc) }
            is EmptyStmt -> {
                goal
            }
            is HavocStmt -> {
                s.ids.forEach {
                    goal.freshConst(it) //just create new constants
                }
                goal
            }
            is IfStmt -> {
                val cond = encodeExpression(s.cond, goal)
                val thenGoal = goal.newGoal()
                val elseGoal = goal.newGoal()
                val merger = goal.newGoal()
                thenGoal.assumptions += cond;
                elseGoal.assumptions += "(not $cond)";
                val finalThenGoal = executeStatement(s.then, thenGoal)
                val finalElseGoal = executeStatement(s.otherwise, elseGoal)

                //FIXME prefix with condition else formula is valid
                merger.assumptions.addAll(finalThenGoal.assumptions)
                merger.assumptions.addAll(finalElseGoal.assumptions)

                merger.assertions.addAll(finalThenGoal.assertions)
                merger.assertions.addAll(finalElseGoal.assertions)

                val allVars = finalElseGoal.signature.keys + finalThenGoal.signature.keys
                allVars.forEach { v ->
                    val vThen = finalThenGoal.currentVar(v)
                    val vElse = finalElseGoal.currentVar(v)
                    if(vThen!=vElse) {//we have to merge
                        val newValue = merger.freshConst(v)
                        merger.assertions += "(= $newValue (ite $cond $vThen $vElse))"
                    }
                }
                merger
            }
            is WhileStmt -> {
                val cond = encodeExpression(s.cond, goal)

                val init = goal.newGoal()
                val preservation = goal.newGoal()
                val termination = goal.newGoal()

                init.assertions += encodeExpression(s.loopInv, goal)
                discharge(init)

                preservation.assumptions.clear()
                preservation.assertions.clear()
                preservation.assumptions += encodeExpression(s.loopInv, preservation)
                preservation.assumptions += encodeExpression(s.cond, preservation)
                s.erase.forEach { preservation.freshConst(it) }
                val afterBody = executeStatement(s.then, preservation)
                afterBody.assertions += encodeExpression(s.loopInv, afterBody)
                discharge(afterBody)

                termination.assumptions.clear()
                termination.assertions.clear()
                s.erase.forEach { termination.freshConst(it) }
                termination.assumptions += encodeExpression(s.loopInv, preservation)
                termination.assumptions += "(not ${encodeExpression(s.cond, preservation)})"
                //discharge(termination)

                termination
            }
        }
    }

    private fun discharge(goal: Goal) {
        print(goal.dischargeIntoSmt())
        dischargedGoals += goal
    }
}