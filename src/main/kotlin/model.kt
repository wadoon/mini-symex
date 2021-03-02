import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 *
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
fun visit(expr: QuantifiedExpr, arg: T): R
}
 */

//region
interface Metadata
data class Position(val source: String, val startOffset: Int, val endOffset: Int) : Metadata
data class Declaration(val position: Position) : Metadata
//endregion

sealed class Node {
    var position: Position? = null
    var named: String? = null
    //abstract fun <T, R> accept(v: Visitor<R, T>, arg: T): R
}

data class Program(val procedures: MutableList<Procedure>) : Node() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class Procedure(
    var name: String, val args: MutableList<Pair<TypeDecl, Variable>>, val body: Body,
    var requires: Expr = BoolLit(true),
    var ensures: Expr = BoolLit(true),
    var modifies: MutableList<Variable> = arrayListOf(),
    var returnType: TypeDecl = TypeDecl("void")
) : Node() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

interface SpecOnly
class DataTypeError(message: String?) : Exception(message) {}

/**
 * The semantic representation of a type. A type is [name] with a [dimension]. If [dimension] is greater than 0,
 * this type is an array type
 */
sealed class Type(val name: String, val dimension: Int = 0) {
    object ANY : Type("any", 0) //special type only available in logic to mark polymorphic operators
    object VOID : Type("void", 0)
    object INT : Type("int", 0)
    object BOOL : Type("bool", 0)
    object INT_ARRAY : Type("int", 1)
    object BOOL_ARRAY : Type("bool", 1)
}


sealed class Expr : Node() {
    fun typeOf(binders: Map<Variable, Type>): Type = when (this) {
        is BinaryExpr -> {
            require(left.typeOf(binders) == op.leftType)
            require(right.typeOf(binders) == op.rightType)
            op.returnType
        }
        is UnaryExpr -> {
            require(right.typeOf(binders) == op.rightType)
            op.type
        }
        is IntLit -> Type.INT
        is BoolLit -> Type.BOOL
        is Variable -> binders[this] ?: throw DataTypeError("Variable ${this.id} has no known type.")
        is FunctionCall -> binders[this.id]?.also {
            if (it == Type.VOID) throw DataTypeError("Function ${this.id.id} has void as return type.")
        } ?: throw DataTypeError("Function ${this.id.id} has no known type.")
        is QuantifiedExpr -> {
            val bt = this.binders.toBinders()
            val b = binders + bt
            if (left.typeOf(b) != Type.BOOL) {
                throw DataTypeError("Expected boolean for expression under forall")
            }
            Type.BOOL
        }
    }
}

fun Iterable<Pair<TypeDecl, Variable>>.toBinders(): Map<Variable, Type> = this.map { (t, v) -> v to t.toType() }.toMap()
fun Iterable<TypeDecl>.toType() = this.map { it.toType() }
fun TypeDecl.toType(): Type =
    when {
        array && name == "int" -> Type.INT_ARRAY
        !array && name == "int" -> Type.INT
        array && name == "bool" -> Type.BOOL_ARRAY
        !array && name == "bool" -> Type.BOOL
        else -> throw IllegalStateException("Type ${name}${if (array) "[]" else ""} is unknown.")
    }

data class QuantifiedExpr(
    val binders: MutableList<Pair<TypeDecl, Variable>>,
    var left: Expr,
    val quantifier: Quantifier
) : Expr(), SpecOnly {
    enum class Quantifier(val smtSymbol: String) {
        FORALL("forall"), EXISTS("exists")
    }
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class BinaryExpr(var left: Expr, var op: Operator, var right: Expr) : Expr() {
    enum class Operator(
        val smtSymbol: String,
        val returnType: Type,
        val leftType: Type = returnType,
        val rightType: Type = returnType
    ) {
        ADD("+", Type.INT),
        SUB("-", Type.INT),
        DIV("div", Type.INT),
        MUL("*", Type.INT),
        MOD("mod", Type.INT),
        EQUAL("=", Type.BOOL, Type.ANY, Type.ANY),
        NOT_EQUAL("n/a", Type.BOOL, Type.ANY, Type.ANY),
        LT("<", Type.BOOL, Type.INT, Type.INT),
        LTE("<=", Type.BOOL, Type.INT, Type.INT),
        GT(">", Type.BOOL, Type.INT, Type.INT),
        GTE(">=", Type.BOOL, Type.INT, Type.INT),
        IMPLIES("=>", Type.BOOL),
        AND("and", Type.BOOL),
        OR("or", Type.BOOL)
    }

    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class UnaryExpr(var op: Operator, var right: Expr) : Expr() {
    enum class Operator(val smtSymbol: String, val type: Type, val rightType: Type = type) {
        SUB("-", Type.INT),
        NEGATE("not", Type.BOOL),
    }

    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class IntLit(var value: BigInteger) : Expr() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class BoolLit(var value: Boolean) : Expr() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class Variable(var id: String) : Expr() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class FunctionCall(var id: Variable, val args: MutableList<Expr>) : Expr() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}


sealed class Statement : Node()
data class HavocStmt(var ids: MutableList<Variable>) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class AssumeStmt(var cond: Expr) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class AssertStmt(var cond: Expr) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class Body(val statements: MutableList<Statement>) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class IfStmt(var cond: Expr, var then: Body, var otherwise: Body) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)

}

data class WhileStmt(
    var cond: Expr, var then: Body,
    var loopInv: Expr = BoolLit(true),
    var erase: MutableList<Variable> = arrayListOf()
) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

class EmptyStmt() : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class AssignStmt(
    var id: Variable, var lhs: Expr,
    var decl: TypeDecl? = null,
    var arrayAccess: Expr? = null
) : Statement() {
    //override fun <T, R> accept(v: Visitor<R, T>, arg: T) = v.visit(this, arg)
}

data class TypeDecl(val name: String, val array: Boolean = false) : Node()
