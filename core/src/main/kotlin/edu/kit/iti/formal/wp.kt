package edu.kit.iti.formal

import edu.kit.iti.formal.BinaryExpr.Operator.EQUAL
import edu.kit.iti.formal.BinaryExpr.Operator.NOT_EQUAL
import edu.kit.iti.formal.UnaryExpr.Operator.NEGATE

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
class WP(private val procedures: List<Procedure> = arrayListOf()) {
    inner class Scope(
        val signature: HashMap<Variable, TypeDecl> = HashMap(),
    ) {
        fun sub() = Scope(
            signature = HashMap(signature)
        )

        fun clone() = Scope(signature = HashMap(signature))

        fun currentVar(id: Variable): String {
            return id.id
        }

        fun introduce(signature: MutableList<Pair<TypeDecl, Variable>>) {
            signature.forEach { (t, v) -> introduce(v, t) }
        }

        fun introduce(v: Variable, t: TypeDecl) {
            this.signature[v] = t
            if (t.array) {
                val (l, t) = getLengthOf(v)
                introduce(l, t)
            }
        }

        fun getLengthOf(v: Variable): Pair<Variable, TypeDecl> {
            val len = Variable(v.id + "\$length")
            val typ = TypeDecl("int", false)
            return len to typ
        }

        fun type(variable: Variable): String {
            return signature[variable]?.toSmtType()
                ?: throw RuntimeException("Unknown variable ${variable.toHuman()}")
        }
    }

    val commands = arrayListOf<String>()

    private fun declareConst(t: Type, v: Variable, i: Int) {
        commands += if (t.dimension == 0)
            "(declare-const ${v.id}_${i} ${t.toSmtType()})\n"
        else
            "(declare-const ${v.id}_${i} (Array Int ${t.toSmtType()}))\n"
        require(t.dimension < 2)
    }

    private fun encodeExpression(expr: Expr, state: Scope): String = encodeExpression(expr, state::currentVar, state)

    private fun encodeExpression(expr: Expr, vars: (Variable) -> String, state: Scope): String = when (expr) {
        is BinaryExpr ->
            if (expr.op == NOT_EQUAL) {
                encodeExpression(UnaryExpr(NEGATE, expr.copy(op = EQUAL)), vars, state)
            } else {
                "(${expr.op.smtSymbol} ${encodeExpression(expr.left, vars, state)} ${
                    encodeExpression(expr.right, vars, state)
                })"
            }
        is FunctionCall -> TODO() //encodeFunctionCallExpression(expr, state)
        is IntLit -> expr.value.toString()
        is UnaryExpr -> "(${expr.op.smtSymbol} ${encodeExpression(expr.right, vars, state)})"
        is Variable -> vars(expr)
        is BoolLit -> expr.value.toString()
        is QuantifiedExpr -> {
            val q = expr.quantifier.smtSymbol
            val b = expr.binders.joinToString(" ") { (t, v) ->
                "(${t.toSmtType()} ${v.id})"
            }
            val s = { a: Variable ->
                if (expr.binders.any { (_, v) -> a == v }) a.id
                else vars(a)
            }
            "($q ($b) ${encodeExpression(expr.sub, s, state)})"
        }
        is ArrayAccess -> {
            expr.args.foldRight(encodeExpression(expr.id, vars, state)) { e, acc ->
                "(select $acc ${encodeExpression(e, vars, state)})"
            }
        }
    }

    fun executeStatements(statements: List<Statement>, state: Scope = Scope()): String {
        return if (statements.isEmpty()) "false"
        else executeStatement(statements.first(), statements.drop(1), state)
    }

    fun executeStatement(s: Statement, tail: List<Statement>, state: Scope = Scope()): String {
        return when (s) {
            is HavocStmt -> {
                val vars = s.ids.joinToString(" ") { v -> "(${v.id} ${state.type(v)})" }
                val body = executeStatements(tail, state)
                "(forall ($vars) $body)"
            }
            is ChooseStmt -> {
                val vars = s.variables.joinToString(" ") { v -> "(${v.id} ${state.type(v)})" }
                val pred = encodeExpression(s.expr, state)
                val body = executeStatements(tail, state)
                "(exists ($vars) (and $pred $body))"
            }
            is AssertStmt -> {
                val e = encodeExpression(s.cond, state)
                    .named(s.named)
                    .position(s.position)
                val body = executeStatements(tail, state)
                //val desc = s.description ?: "assert '${s.cond.toHuman()}' @ ${s.position}"
                "(or (not $e) (=> $e $body))"
            }
            is AssumeStmt -> {
                //val desc = s.description ?: "assume '${s.cond.toHuman()}' @ ${s.position}"
                val e = encodeExpression(s.cond, state)
                val body = executeStatements(tail, state)
                "(=> $e $body)"
            }
            is AssignStmt -> handleAssignment(s, tail, state)
            is Body -> executeStatements(tail, state)
            is EmptyStmt -> {
                executeStatements(tail, state)
            }
            is IfStmt -> {
                //evaluate condition in the current goal
                val cond = encodeExpression(s.cond, state)
                // we split the goal into three subgoals:
                val thenGoal = state.sub()   // (1) new scopes of the then-branch
                val elseGoal = state.sub()   // (2) new scopes of the else-branch

                val thenBody = executeStatements(s.then.statements + tail, thenGoal)
                val elseBody = executeStatements(s.otherwise.statements + tail, elseGoal)
                "(and (=> $cond $thenBody) (=> (not $cond) $elseBody))"
            }
            is WhileStmt -> {
                TODO()
                /*isolatedGoal {
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
                    val afterBody = executeStatement(s.body, preservation)
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
                termination*/
            }
        }
    }

    private fun encodeExpression(clauses: Clauses, state: Scope): String =
        encodeExpression(clauses, state::currentVar, state)


    private fun handleAssignment(s: AssignStmt, tail: List<Statement>, state: Scope): String {
        s.decl?.let { state.signature[s.id] = it }
        fun liftToArray(v: String, expr: String) =
            s.arrayAccess?.let {
                val arrayExpr = encodeExpression(it, state)
                "(store ${v} $arrayExpr $expr)"
            } ?: expr


        val rhs = s.rhs
        val body = executeStatements(tail, state)
        var boundedValue = ""
        val boundedVariable = s.id.toHuman()

        if (rhs is FunctionCall) {
            val rt = "_ret_"
            val function = procedures.find { it.name == rhs.id.id }
            require(function != null)
            val params: List<String> = function.args.map { (_, v) -> v.id }
            val precondVars = rhs.args.zip(params).joinToString(" ") { (e, p) ->
                "($p ${encodeExpression(e, state)})"
            }
            val precond = "(let ($precondVars) ${encodeExpression(function.requires, state)})"
            val postCond = encodeExpression(
                function.ensures,
                { v -> if (v.id == "__retValue__") rt else state.currentVar(v) },
                state
            )

            val e = liftToArray(boundedVariable, rt)
            val main = "(forall (($rt ${function.returnType.toSmtType()}))" +
                    "(=> $postCond (let (($boundedVariable $e)) $body))"
            return "(or $precond $main)"
            //    return "(or $precond $body)"
        } else if (rhs != null) {
            val rhsExpr = liftToArray(boundedVariable, encodeExpression(rhs, state))
            return "(let (($boundedVariable $rhsExpr)) $body)"
        } else {
            return body
        }
    }

    private fun encodeExpression(clauses: Clauses, lookup: (Variable) -> String, scope: Scope): String {
        val namedExpr = clauses.map { (name, expr) ->
            encodeExpression(expr, lookup, scope).named(name?.id)
        }
        return when {
            namedExpr.isEmpty() -> "true"
            namedExpr.size == 1 -> namedExpr.first()
            else -> "(and ${namedExpr.joinToString(" ")})"
        }
    }

    fun proveBody(function: Procedure) {
        val proofObligation = Body(arrayListOf())
        val scope = Scope()
        scope.introduce(function.signature)
        proofObligation.statements.add(AssumeStmt(function.requires, "pre-condition of ${function.name}"))
        proofObligation.statements.add(function.body)
        proofObligation.statements.add(AssertStmt(function.ensures, "post-condition of ${function.name}"))
        executeStatements(function.body.statements, scope)
    }
}
