package edu.kit.iti.formal

import edu.kit.iti.formal.BinaryExpr.Operator.EQUAL
import edu.kit.iti.formal.BinaryExpr.Operator.NOT_EQUAL
import edu.kit.iti.formal.UnaryExpr.Operator.NEGATE
import java.io.PrintWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
var PRINT_ATTRIBUTES = true

object VariableCounter {
    private val counters = HashMap<String, Int>()
    fun fresh(name: String): Int {
        counters[name] = counters.getOrDefault(name, 0) + 1
        return counters[name]!!
    }
}

class SymEx2(private val procedures: List<Procedure> = arrayListOf()) {
    inner class Scope(
        val signature: MutableMap<Variable, TypeDecl> = HashMap(),
        //private val variables: MutableMap<Variable, MutableList<Int>> = HashMap(),
        private val variables: MutableMap<Variable, Int> = HashMap(),
        private val global: MutableSet<Variable> = HashSet(),
        private val parent: Scope? = null
    ) {
        fun sub() = Scope(
            signature = HashMap(signature),
            variables = HashMap(variables),
            global = global,
            parent = parent
        )

        fun makeAllKnownVariablesGlobal() = global.addAll(signature.keys)

        fun clone() = Scope(signature = HashMap(signature), variables = HashMap(variables))

        fun currentVar(id: Variable): String {
            //val cnt = variables.computeIfAbsent(id) { arrayListOf(0) }.last()
            val cnt = variables[id]
            return "${id.id}_${cnt}"
        }

        fun freshConst(id: Variable): String {
            //val cnt = variables.computeIfAbsent(id) { arrayListOf(0) }
            //val fresh = cnt.last() + 1
            val fresh = VariableCounter.fresh(id.id)
            variables[id] = fresh
            //cnt.add(fresh)

            val t = signature[id] ?: error("Variable $id not declared")
            declareConst(t.toType(), id, fresh)
            return currentVar(id)
        }

        fun introduce(signature: MutableList<Pair<TypeDecl, Variable>>, global: Boolean = false) {
            signature.forEach { (t, v) -> introduce(v, t, global) }
        }

        fun introduce(v: Variable, t: TypeDecl, global: Boolean = false) {
            this.signature[v] = t
            if (global) {
                this.global.add(v)
            }
            if (t.array) {
                val (l, t) = getLengthOf(v);
                introduce(l, t)
            }
        }

        fun getLengthOf(v: Variable): Pair<Variable, TypeDecl> {
            val len = Variable(v.id + "\$length")
            val typ = TypeDecl("int", false)
            return len to typ
        }

        fun smtType(variable: Variable) = type(variable).toSmtType()

        fun type(variable: Variable): TypeDecl {
            return signature[variable]
                ?: throw RuntimeException("Unknown variable ${variable.toHuman()}")
        }
    }

    private var currentReturnVariable: Variable? = null
    private val vcgGenerated = HashSet<String>()

    val commands = arrayListOf<String>()

    private fun declareConst(t: Type, v: Variable, i: Int? = null) {
        val name = if (i == null) v.id else "${v.id}_$i"
        commands += if (t.dimension == 0)
            "(declare-const $name ${t.toSmtType()})\n"
        else
            "(declare-const $name (Array Int ${t.toSmtType()}))\n"
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
        val ret = fn()
        commands += ";;; -- End of $name --------------------------------"
        return ret
    }

    private fun <T> isolatedGoal(name: String = "", fn: () -> T): T {
        //commands += ";;; -- $name --------------------------------"
        commands += "(push 1)"
        commands += "(echo \"$name\")"
        val scope = fn()
        commands += "(pop 1)"
        return scope
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
        is FunctionCall -> encodeFunctionCallExpression(expr, state)
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
        is DoubleLit -> expr.value
        is TypeCast -> when (expr.type.toType()) {
            Type.INT -> "(to_int ${encodeExpression(expr.sub, state)})"
            Type.BOOL -> "(= 1 ${encodeExpression(expr.sub, state)})"
            Type.DOUBLE -> "(to_real ${encodeExpression(expr.sub, state)})"
            else -> TODO()
        }
        is ArrayInit -> {
            var s = "empty";
            expr.values.forEachIndexed { index, expr ->
                s = "(store $s $index ${encodeExpression(expr, state)})"
            }
            s
        }
    }

    fun executeStatement(s: Statement, state: Scope = Scope()): Scope {
        return when (s) {
            is ChooseStmt -> {
                error("choose statement not possible with this engine")
            }
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
                        if (expr is FunctionCall) {
                            encodeFunctionCallExpression(expr, state)
                        } else {
                            encodeExpression(expr, state)
                        }

                    val value = s.arrayAccess?.let {
                        val arrayExpr = encodeExpression(it, state)
                        "(store ${state.currentVar(s.id)} $arrayExpr $rhs)"
                    } ?: rhs

                    val fresh = state.freshConst(lhs)
                    assume("(= $fresh $value)")
                }
                state
            }
            is Body ->
                s.statements.fold(state) { acc, statement ->
                    //println(statement)
                    executeStatement(statement, acc)
                }
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
                val branchConditionVariable = Variable("__branch__cond_${s.position?.startLine}_${cnt++}")
                state.introduce(branchConditionVariable, TypeDecl("bool"))
                declareConst(Type.BOOL, branchConditionVariable)

                //evaluate condition in the current goal
                val pureCond = encodeExpression(s.cond, state)
                val cond = "(or ${branchConditionVariable.id} $pureCond)"
                val notCond = "(or ${branchConditionVariable.id} (not $pureCond))"

                // we split the goal into three subgoals:
                val thenGoal = state.sub()   // (1) new scopes of the then-branch
                val elseGoal = state.sub()   // (2) new scopes of the else-branch
                val afterIf = state.sub()    // (3) new scopes after if-branch


                // assume that the guard holds in the then-branch
                val finalThenGoal = sideGoal("Then-Branch: Line ${s.then.position?.startLine}") {
                    assume(cond)
                    executeStatement(s.then, thenGoal)
                }

                // assume that the guard does not hold in the then-branch
                val elseBody = s.otherwise
                val finalElseGoal = sideGoal("Else-Branch: Line ${s.otherwise.position?.startLine}") {
                    assume(notCond)
                    executeStatement(elseBody, elseGoal)
                }

                assume("(= ${branchConditionVariable.id} true)")

                val allVars = finalThenGoal.signature.keys + finalElseGoal.signature.keys
                allVars.forEach { v ->
                    val vThen = finalThenGoal.currentVar(v)
                    val vElse = finalElseGoal.currentVar(v)
                    if (vThen != vElse) {// Conflict found: We have to merge
                        val newValue = afterIf.freshConst(v)
                        assume("(= $newValue (ite $pureCond $vThen $vElse))")
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
                termination
            }
            is ProcedureCall -> {
                // 1. Find procedure within the program
                val procedure = procedures.find { it.name == s.id.id }
                    ?: error("Could not find procedure with name ${s.id.id} amongst ${procedures.joinToString(", ") { it.name }}")
                // 2. Map arguments
                val bodyGoal = state.sub()
                for ((param, arg) in procedure.args.zip(s.args)) {
                    val variable = bodyGoal.freshConst(param.second)
                    assume("(= $variable ${encodeExpression(arg, state)}")
                }
                currentReturnVariable = Variable("__retValue__${procedure.name}_${cnt++}")
                bodyGoal.introduce(currentReturnVariable!!, procedure.returnType)
                // 3. Proceed with the body of the procedure
                executeStatement(procedure.body, bodyGoal)
                state
            }
            is ReturnStmt -> {
                if (currentReturnVariable != null && state.type(currentReturnVariable!!).toType() != Type.VOID) {
                    val fresh = state.freshConst(currentReturnVariable!!)
                    assume("(= $fresh ${encodeExpression(s.expr, state)})")
                }
                state
            }
        }
    }

    private fun encodeExpression(clauses: Clauses, scope: Scope): String {
        val namedExpr = clauses.map { (name, expr) ->
            encodeExpression(expr, scope).named(name?.id)
        }
        return if (namedExpr.isEmpty()) "true"
        else "(and ${namedExpr.joinToString(" ")})"
    }

    private fun encodeFunctionCallExpression(expr: FunctionCall, state: Scope) =
        encodeFunctionCallExpression(expr.id.id, expr.args, state)

    private fun encodeFunctionCallExpression(name: String, args: List<Expr>, state: Scope): String {
        val function = procedures.find { it.name == name }
        require(function != null)

        if (function.hasContracts()) {
            // Prove the function behind the function call
            if (function.name !in vcgGenerated) {
                proveBody(function)
            }

            // reduce the arguments to single variables (introduce assignments)
            isolatedGoal {
                val sig = state.clone()

                val params: List<String> = function.args.map { (t, v) ->
                    sig.signature[v] = t
                    sig.freshConst(v)
                }

                args.zip(params).forEach { (e, p) ->
                    assume("(= $p ${encodeExpression(e, state)})")
                }

                // discharge the precondition
                assert(encodeExpression(function.requires, sig))
                checkSat()
            }

            if (function.returnType.toType() != Type.VOID) {
                val variable = Variable("__retValue__${function.name}_${cnt++}")
                state.signature[variable] = function.returnType
                val retValue = state.freshConst(variable)
                assume(
                    "(= $retValue ${encodeExpression(function.ensures, state)})",
                    name = "Post-condition of ${function.name}"
                )
                return retValue
            }
        } else {
            return encodeFunctionCallExpressionEmbedded(function, args, state)
        }
        return ""
    }

    private fun encodeFunctionCallExpressionEmbedded(
        function: Procedure,
        args: List<Expr>,
        state: SymEx2.Scope
    ): String {
        if (function.returnType.toType() == Type.VOID)
            error("Function call in expression of void function: ${function.name}")
        val subState = state.sub()
        for ((param, arg) in function.args.zip(args)) {
            subState.introduce(param.second, param.first)
            val variable = subState.freshConst(param.second)
            assume("(= $variable ${encodeExpression(arg, state)}")
        }
        currentReturnVariable = Variable("__retValue__${function.name}_${cnt++}")
        subState.introduce(currentReturnVariable!!, function.returnType)
        executeStatement(function.body, subState)
        return currentReturnVariable!!.id
    }

    var cnt = 0

    fun proveBody(function: Procedure, scope: Scope = Scope()) {
        val proofObligation = Body(arrayListOf())
        scope.introduce(function.signature)
        proofObligation.statements.add(AssumeStmt(function.requires, "pre-condition of ${function.name}"))
        proofObligation.statements.add(function.body)
        proofObligation.statements.add(AssertStmt(function.ensures, "post-condition of ${function.name}"))
        executeStatement(function.body, scope)
    }

    fun encodeInto(out: PrintWriter) {
        commands.forEach { out.println(it) }
    }
}

private fun Procedure.hasContracts(): Boolean = ensures.isNotEmpty() || requires.isNotEmpty()


fun String.named(s: String?): String = if (PRINT_ATTRIBUTES && s != null) "(! $this :named \"$s\")" else this
fun String.position(p: Position?): String =
    if (PRINT_ATTRIBUTES && p != null) "(! $this :source-file \"${p.source}\" :start ${p.startOffset} :end ${p.endOffset})" else this


fun TypeDecl.toSmtType(): String = toType().toSmtType()
fun Type.toSmtType(): String = when (this) {
    Type.VOID, Type.ANY -> error("No SMT type for Void or ANY")
    Type.BOOL_ARRAY -> "(Array Int Bool)"
    Type.INT_ARRAY -> "(Array Int Int)"
    Type.INT -> "Int"
    Type.BOOL -> "Bool"
    Type.DOUBLE -> "Real"
    Type.DOUBLE_ARRAY -> "(Array Int Real)"
}