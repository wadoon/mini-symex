package edu.kit.iti.formal

import TinyCBaseVisitor
import TinyCLexer
import TinyCParser
import edu.kit.iti.formal.QuantifiedExpr.Quantifier.*
import edu.kit.iti.formal.UnaryExpr.Operator.*
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ParserRuleContext

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */

object CParsingFacade {
    @JvmStatic
    fun parseProgram(stream: CharStream): Program {
        val lexer = TinyCLexer(stream)
        val parser = TinyCParser(CommonTokenStream(lexer))
        val ctx = parser.program()

        require(parser.numberOfSyntaxErrors == 0) {
            "Syntax Errors!"
        }

        return ctx.accept(TinyCAstTranslator()) as Program
    }
}

private class TinyCAstTranslator : TinyCBaseVisitor<Node>() {
    private fun <T : Node> T.withPosition(ctx: ParserRuleContext): T {
        val source = ctx.start.tokenSource.sourceName

        this.position = Position(
            source,
            startOffset = ctx.start.startIndex,
            endOffset = ctx.stop.stopIndex,
            startLine = ctx.start.line,
            startInLine = ctx.start.charPositionInLine,
            endLine = ctx.stop.line,
            endInLine = ctx.stop.charPositionInLine,
        )
        return this
    }

    override fun visitProgram(ctx: TinyCParser.ProgramContext): Node {
        return Program(map(ctx.procedure()))
            .withPosition(ctx)
    }

    private fun <T> map(ctx: List<ParserRuleContext>) =
        ctx.map { it.accept(this) as T }.toMutableList()


    override fun visitQuantifiedExpr(ctx: TinyCParser.QuantifiedExprContext): Node =
        QuantifiedExpr(
            binders(ctx.binders()), ctx.expr().accept(this) as Expr,
            if (ctx.q.text.last() == 's') EXISTS else FORALL
        ).withPosition(ctx)


    override fun visitLetExpr(ctx: TinyCParser.LetExprContext?): Node {
        TODO()
    }

    override fun visitArrayaccess(ctx: TinyCParser.ArrayaccessContext) =
        ArrayAccess(ctx.id().accept(this) as Variable, exprList(ctx.exprList()))
            .withPosition(ctx)


    override fun visitProcedure(ctx: TinyCParser.ProcedureContext): Node {
        val b = ctx.body().accept(this) as Body
        val args = binders(ctx.a)

        return Procedure(
            name = ctx.name.text,
            signature = arrayListOf(),
            args = args,
            body = b,
            requires = ctx.pre?.accept(this) as? Clauses? ?: Clauses(),
            ensures = ctx.post?.accept(this) as? Clauses? ?: Clauses(),
            modifies = variables(ctx.modifies)
        ).withPosition(ctx)
    }

    private fun binders(ctx: TinyCParser.BindersContext?): MutableList<Pair<TypeDecl, Variable>> =
        if (ctx == null) arrayListOf()
        else {
            (0 until ctx.id().size).map {
                type(ctx.type(it)) as TypeDecl to
                        ctx.id(it).accept(this) as Variable
            }.toMutableList()
        }

    private fun variables(ctx: TinyCParser.IdsContext?): MutableList<Variable> =
        if (ctx == null) arrayListOf()
        else ctx.id()?.map { (it.accept(this) as Variable).withPosition(ctx) }?.toMutableList() ?: arrayListOf()

    override fun visitUnary(ctx: TinyCParser.UnaryContext) = UnaryExpr(
        if (ctx.op.text == "!") NEGATE else SUB,
        ctx.expr().accept(this) as Expr
    ).withPosition(ctx)

    val TRUE = BoolLit(true)

    override fun visitIfStatement(ctx: TinyCParser.IfStatementContext): Node {
        return IfStmt(
            ctx.expr().accept(this) as Expr,
            body(ctx.statement(0)),
            body(ctx.statement(1))
        ).withPosition(ctx)

    }

    private fun body(statement: TinyCParser.StatementContext?): Body {
        val b = Body(arrayListOf())
        if (statement == null) return b
        b.withPosition(statement)

        val s = statement.accept(this) as Statement
        return if (s is Body) s else b.also { b.statements.add(s) }

    }

    override fun visitWhileStatement(ctx: TinyCParser.WhileStatementContext) = WhileStmt(
        ctx.cond.accept(this) as Expr,
        body(ctx.statement()),
        ctx.invariant?.accept(this) as Clauses? ?: Clauses(),
        erase = variables(ctx.variant),
        label = ctx.label?.text
    ).withPosition(ctx)

    override fun visitBody(ctx: TinyCParser.BodyContext) = Body(map(ctx.statement())).withPosition(ctx)

    override fun visitAssignment(ctx: TinyCParser.AssignmentContext) = AssignStmt(
        ctx.id().accept(this) as Variable,
        ctx.rhs?.accept(this) as Expr?,
        type(ctx.type()),
        arrayAccess = ctx.aa?.accept(this) as Expr?
    ).withPosition(ctx)

    private fun type(type: TinyCParser.TypeContext?): TypeDecl? {
        if (type == null) return null
        return TypeDecl(type.t.text, type.a != null).withPosition(type)
    }

    override fun visitBool(ctx: TinyCParser.BoolContext): Node = BoolLit(ctx.BOOL().text == "true").withPosition(ctx)

    override fun visitExpr(ctx: TinyCParser.ExprContext): Node {
        if (ctx.primary() != null) {
            try {
                return ctx.primary().accept(this)
            } catch (e: NullPointerException) {
                println(ctx.text)
                throw e
            }
        }
        return BinaryExpr(
            ctx.expr(0).accept(this) as Expr,
            binaryOperator(ctx.op.text),
            ctx.expr(1).accept(this) as Expr
        ).withPosition(ctx)
    }

    private fun binaryOperator(text: String): BinaryExpr.Operator =
        when (text) {
            "+" -> BinaryExpr.Operator.ADD
            "-" -> BinaryExpr.Operator.SUB
            "*" -> BinaryExpr.Operator.MUL
            "/" -> BinaryExpr.Operator.DIV
            "%" -> BinaryExpr.Operator.MOD
            "<" -> BinaryExpr.Operator.LT
            "<=" -> BinaryExpr.Operator.LTE
            ">" -> BinaryExpr.Operator.GT
            ">=" -> BinaryExpr.Operator.GTE
            "==" -> BinaryExpr.Operator.EQUAL
            "!=" -> BinaryExpr.Operator.NOT_EQUAL
            "&&" -> BinaryExpr.Operator.AND
            "||" -> BinaryExpr.Operator.OR
            "==>" -> BinaryExpr.Operator.IMPLIES
            else -> throw IllegalArgumentException("Unknown operator '$text'.")
        }

    override fun visitInteger(ctx: TinyCParser.IntegerContext) = IntLit(ctx.INT().text.toBigInteger()).withPosition(ctx)

    override fun visitFcall(ctx: TinyCParser.FcallContext) = FunctionCall(
        ctx.id().accept(this) as Variable,
        exprList(ctx.exprList())
    ).withPosition(ctx)

    private fun exprList(ctx: TinyCParser.ExprListContext): MutableList<Expr> = map(ctx.expr())


    override fun visitEmptyStmt(ctx: TinyCParser.EmptyStmtContext) = EmptyStmt().withPosition(ctx)
    override fun visitAssert_(ctx: TinyCParser.Assert_Context) =
        AssertStmt(createClauses(ctx.expr().accept(this) as Expr)).withPosition(ctx)

    private fun createClauses(expr: Expr) = Clauses(arrayListOf(null to expr))

    override fun visitAssume(ctx: TinyCParser.AssumeContext) =
        AssumeStmt(createClauses(ctx.expr().accept(this) as Expr)).withPosition(ctx)

    override fun visitHavoc(ctx: TinyCParser.HavocContext) = HavocStmt(
        ctx.ids().id().map { it.accept(this) as Variable }.toMutableList()
    ).withPosition(ctx)

    override fun visitId(ctx: TinyCParser.IdContext) = Variable(ctx.IDENTIFIER().text)


    override fun visitChoose(ctx: TinyCParser.ChooseContext): Node
        = ChooseStmt(ctx.id() as Variable, ctx.expr() as Expr).withPosition(ctx)
}