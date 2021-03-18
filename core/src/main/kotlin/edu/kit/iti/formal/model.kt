package edu.kit.iti.formal

import java.math.BigInteger

//region
interface Metadata
data class Position(
    val source: String, val startOffset: Int, val endOffset: Int,
    val startLine: Int = 0, val startInLine: Int = 0,
    val endLine: Int = 0, val endInLine: Int = 0
) : Metadata {
    override fun toString(): String = "@($startLine,$startInLine)"
}

data class Declaration(val position: Position) : Metadata
//endregion

sealed class Node {
    var position: Position? = null
    var named: String? = null
}

data class Program(val procedures: MutableList<Procedure>) : Node() {
}

data class Procedure(
    var name: String,
    val signature: MutableList<Pair<TypeDecl, Variable>>,
    val args: MutableList<Pair<TypeDecl, Variable>>,
    val body: Body,
    var requires: Clauses = Clauses(),
    var ensures: Clauses = Clauses(),
    var modifies: MutableList<Variable> = arrayListOf(),
    var returnType: TypeDecl = TypeDecl("void")
) : Node() {
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


sealed class Expr : Node()

data class QuantifiedExpr(
    val binders: MutableList<Pair<TypeDecl, Variable>>,
    var sub: Expr,
    val quantifier: Quantifier
) : Expr(), SpecOnly {
    enum class Quantifier(val smtSymbol: String) {
        FORALL("forall"), EXISTS("exists")
    }
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
}

data class UnaryExpr(var op: Operator, var right: Expr) : Expr() {
    enum class Operator(val smtSymbol: String, val type: Type, val rightType: Type = type) {
        SUB("-", Type.INT),
        NEGATE("not", Type.BOOL),
    }
}

data class IntLit(var value: BigInteger) : Expr()

data class BoolLit(var value: Boolean) : Expr()

data class Variable(var id: String) : Expr()

data class FunctionCall(var id: Variable, val args: MutableList<Expr>) : Expr()

data class ArrayAccess(var id: Variable, val args: MutableList<Expr>) : Expr()

data class Clauses(private val intern: MutableList<Pair<Variable?, Expr>> = arrayListOf()) :
    MutableList<Pair<Variable?, Expr>> by intern,
    Node()

sealed class Statement : Node()
data class HavocStmt(var ids: MutableList<Variable>) : Statement()

data class AssumeStmt(var cond: Clauses) : Statement() {
    var description: String? = null

    constructor(cond: Clauses, desc: String) : this(cond) {
        description = desc
    }
}

data class AssertStmt(var cond: Clauses) : Statement() {
    var description: String? = null

    constructor(cond: Clauses, desc: String) : this(cond) {
        description = desc
    }

}

data class Body(val statements: MutableList<Statement>) : Statement()

data class IfStmt(var cond: Expr, var then: Body, var otherwise: Body) : Statement()

data class WhileStmt(
    var cond: Expr, var then: Body,
    var loopInv: Clauses = Clauses(),
    var erase: MutableList<Variable> = arrayListOf()
) : Statement()

class EmptyStmt : Statement()

data class AssignStmt(
    var id: Variable,
    var rhs: Expr?,
    var decl: TypeDecl? = null,
    var arrayAccess: Expr? = null
) : Statement()

data class TypeDecl(val name: String, val array: Boolean = false) : Node()


fun Expr.typeOf(binders: Map<Variable, Type>): Type = when (this) {
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
        if (sub.typeOf(b) != Type.BOOL) {
            throw DataTypeError("Expected boolean for expression under forall")
        }
        Type.BOOL
    }
    is ArrayAccess -> binders[this.id]?.let {
        require(it.dimension > 0) { "Not array" }
        it.toBaseType()
    } ?: throw DataTypeError("Variable ${this.id} has no known type.")
}

fun Type.toBaseType() = when (this) {
    Type.BOOL_ARRAY -> Type.BOOL
    Type.INT_ARRAY -> Type.INT
    else -> this
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


fun Expr.toHuman(): String = when (this) {
    is BinaryExpr -> "(${left.toHuman()} $op ${right.toHuman()})"
    is BoolLit -> value.toString()
    is FunctionCall -> TODO()
    is IntLit -> value.toString()
    is QuantifiedExpr -> "(\\${quantifier.smtSymbol}  ${binders.joinToString(", ") { (a, b) -> "${a.name} ${b.id}" }} ${sub.toHuman()})"
    is UnaryExpr -> "($op ${right.toHuman()})"
    is Variable -> id
    is ArrayAccess -> TODO()
}

internal fun Clauses.toHuman(): String =
    joinToString { (v, t) -> (v?.toHuman() ?: "<empty>") + ":" + t.toHuman() }
