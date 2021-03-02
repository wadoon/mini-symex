import QuantifiedExpr.Quantifier.EXISTS
import QuantifiedExpr.Quantifier.FORALL
import UnaryExpr.Operator.NEGATE
import UnaryExpr.Operator.SUB
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ParserRuleContext

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */

object ParsingFacade {
    @JvmStatic
    fun parseProgram(stream: CharStream): Program {
        val lexer = tinycLexer(stream)
        val parser = tinycParser(CommonTokenStream(lexer))
        val ctx = parser.program()

        require(parser.numberOfSyntaxErrors == 0) {
            "Syntax Errors!"
        }

        return ctx.accept(AstTranslator()) as Program
    }
}

private class AstTranslator : tinycBaseVisitor<Node>() {
    private fun <T : Node> T.withPosition(ctx: ParserRuleContext): T {
        val source = ctx.start.tokenSource.sourceName
        val start = ctx.start.startIndex
        val stop = ctx.stop.stopIndex
        this.position = Position(source, start, stop)
        return this
    }

    override fun visitProgram(ctx: tinycParser.ProgramContext): Node {
        return Program(map(ctx.procedure()))
            .withPosition(ctx)
    }

    private fun <T> map(ctx: List<ParserRuleContext>) =
        ctx.map { it.accept(this) as T }.toMutableList()


    override fun visitQuantifiedExpr(ctx: tinycParser.QuantifiedExprContext): Node =
        QuantifiedExpr(
            binders(ctx.binders()), ctx.expr().accept(this) as Expr,
            if (ctx.q.text.last() == 's') EXISTS else FORALL
        ).withPosition(ctx)


    override fun visitLetExpr(ctx: tinycParser.LetExprContext?): Node {
        TODO()
    }

    override fun visitArrayaccess(ctx: tinycParser.ArrayaccessContext?): Node {
        TODO()
    }

    override fun visitProcedure(ctx: tinycParser.ProcedureContext): Node {
        val b = ctx.body().accept(this) as Body
        val args = binders(ctx.a)

        return Procedure(
            ctx.name.text, args, b,
            requires = ctx.pre?.accept(this) as? Expr? ?: TRUE,
            ensures = ctx.post?.accept(this) as? Expr? ?: TRUE,
            modifies = variables(ctx.modifies)
        ).withPosition(ctx)
    }

    private fun binders(ctx: tinycParser.BindersContext?): MutableList<Pair<TypeDecl, Variable>> =
        if (ctx == null) arrayListOf()
        else {
            (0 until ctx.id().size).map {
                ctx.type(it).accept(this) as TypeDecl to
                        ctx.id(it).accept(this) as Variable
            }.toMutableList()
        }

    private fun variables(ctx: tinycParser.IdsContext?): MutableList<Variable> =
        if (ctx == null) arrayListOf()
        else ctx.id()?.map { (it.accept(this) as Variable).withPosition(ctx) }?.toMutableList() ?: arrayListOf()

    override fun visitUnary(ctx: tinycParser.UnaryContext) = UnaryExpr(
        if (ctx.op.text == "!") NEGATE else SUB,
        ctx.expr().accept(this) as Expr
    ).withPosition(ctx)

    val TRUE = BoolLit(true)

    override fun visitIfStatement(ctx: tinycParser.IfStatementContext): Node {
        return IfStmt(
            ctx.expr().accept(this) as Expr,
            body(ctx.statement(0)),
            body(ctx.statement(1))
        ).withPosition(ctx)

    }

    private fun body(statement: tinycParser.StatementContext?): Body {
        val b = Body(arrayListOf())
        if (statement == null) return b
        b.withPosition(statement)

        val s = statement.accept(this) as Statement
        return if (s is Body) s else b.also { b.statements.add(s) }

    }

    override fun visitWhileStatement(ctx: tinycParser.WhileStatementContext) = WhileStmt(
        ctx.cond.accept(this) as Expr,
        body(ctx.statement()),
        ctx.invariant?.accept(this) as Expr,
        erase = variables(ctx.variant)
    ).withPosition(ctx)

    override fun visitBody(ctx: tinycParser.BodyContext) = Body(map(ctx.statement())).withPosition(ctx)

    override fun visitAssignment(ctx: tinycParser.AssignmentContext) = AssignStmt(
        ctx.id().accept(this) as Variable,
        ctx.rhs.accept(this) as Expr,
        type(ctx.type()),
    ).withPosition(ctx)

    private fun type(type: tinycParser.TypeContext?): TypeDecl? {
        if (type == null) return null
        return TypeDecl(type.t.text, type.a != null).withPosition(type)
    }

    override fun visitBool(ctx: tinycParser.BoolContext): Node = BoolLit(ctx.BOOL().text == "true").withPosition(ctx)

    override fun visitExpr(ctx: tinycParser.ExprContext): Node {
        if (ctx.primary() != null) {
            try {
                return ctx.primary().accept(this)
            } catch (e: NullPointerException) {
                println(ctx.text)
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

    override fun visitInteger(ctx: tinycParser.IntegerContext) = IntLit(ctx.INT().text.toBigInteger()).withPosition(ctx)

    override fun visitFcall(ctx: tinycParser.FcallContext) = FunctionCall(
        ctx.id().accept(this) as Variable,
        map(ctx.expr())
    ).withPosition(ctx)

    override fun visitEmptyStmt(ctx: tinycParser.EmptyStmtContext) = EmptyStmt().withPosition(ctx)
    override fun visitAssert_(ctx: tinycParser.Assert_Context) =
        AssertStmt(ctx.expr().accept(this) as Expr).withPosition(ctx)

    override fun visitAssume(ctx: tinycParser.AssumeContext) =
        AssumeStmt(ctx.expr().accept(this) as Expr).withPosition(ctx)

    override fun visitHavoc(ctx: tinycParser.HavocContext) = HavocStmt(
        ctx.ids().id().map { it.accept(this) as Variable }.toMutableList()
    ).withPosition(ctx)

    override fun visitId(ctx: tinycParser.IdContext) = Variable(ctx.IDENTIFIER().text)
}