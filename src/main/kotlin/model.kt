import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
interface Visitor<R, T> {
    fun visit(program: Program, arg: T): R
    fun visit(program: Procedure, arg: T): R
    fun visit(binaryExpr: BinaryExpr, arg: T): R
    fun visit(unaryExpr: UnaryExpr, arg: T): R
    fun visit(intLit: IntLit, arg: T): R
    fun visit(variable: Variable, arg: T): R
    fun visit(havocStmt: HavocStmt, arg: T): R
    fun visit(functionCall: FunctionCall, arg: T): R
    fun visit(assumeStmt: AssumeStmt, arg: T): R
    fun visit(assertStmt: AssertStmt, arg: T): R
    fun visit(body: Body, arg: T): R
    fun visit(ifStmt: IfStmt, arg: T): R
    fun visit(whileStmt: WhileStmt, arg: T): R
    fun visit(emptyStmt: EmptyStmt, arg: T): R
    fun visit(assignStmt: AssignStmt, arg: T): R
    fun visit(boolLit: BoolLit, arg: T): R
}

sealed class Node {
    abstract fun <T, R> accept(v: Visitor<R, T>, arg: T): R
}

data class Program(val procedures: MutableList<Procedure>) : Node() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class Procedure(
    var name: String, val args: MutableList<Variable>, val body: Body,
    var requires: Expr = BoolLit(true),
    var ensures: Expr = BoolLit(true),
    var modifies: MutableList<Variable> = arrayListOf(),
    var returnType: Type = Type("void")
) : Node() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

sealed class Expr : Node()
data class BinaryExpr(var left: Expr, var op: String, var right: Expr) : Expr() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class UnaryExpr(var op: String, var right: Expr) : Expr() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class IntLit(var value: BigInteger) : Expr() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class BoolLit(var value: Boolean) : Expr() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class Variable(var id: String) : Expr() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class FunctionCall(var id: String, val args: MutableList<Expr>) : Expr() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}


sealed class Statement : Node()
data class HavocStmt(var ids: MutableList<Variable>) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class AssumeStmt(var cond: Expr) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class AssertStmt(var cond: Expr) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class Body(val statements: MutableList<Statement>) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class IfStmt(var cond: Expr, var then: Body, var otherwise: Body) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class WhileStmt(
    var cond: Expr, var then: Body,
    var loopInv: Expr = BoolLit(true),
    var erase: MutableList<Variable> = arrayListOf()
) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

class EmptyStmt() : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class AssignStmt(
    var id: Variable, var lhs: Expr,
    var decl: Type? = null,
    var arrayAccess: Expr? = null
) : Statement() {
    override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class Type(val name: String, val array: Boolean = false)
