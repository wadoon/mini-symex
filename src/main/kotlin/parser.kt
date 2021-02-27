import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.tree.ParseTree

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
        return ctx.accept(AstTranslator()) as Program
    }
}

private class AstTranslator : tinycBaseVisitor<Node>() {
    override fun visitProgram(ctx: tinycParser.ProgramContext): Node {
        return Program(map(ctx.procedure()))
    }

    private fun <T> map(ctx: List<ParserRuleContext>) =
        ctx.map { it.accept(this) as T }.toMutableList()



    override fun visitProcedure(ctx: tinycParser.ProcedureContext): Node {
        val b = ctx.body().accept(this) as Body
        val args = variables(ctx.a)

        return Procedure(
            ctx.name.text, args, b,
            requires = ctx.pre?.accept(this) as? Expr? ?: TRUE,
            ensures = ctx.post?.accept(this) as? Expr? ?: TRUE,
            modifies = variables(ctx.modifies)
        )
    }

    private fun variables(ctx: tinycParser.ArgsContext?) : MutableList<Variable> =
        if(ctx==null) arrayListOf()
        else ctx.id()?.map { it.accept(this) as Variable }?.toMutableList() ?: arrayListOf()

    val TRUE = BoolLit(true)

    override fun visit(tree: ParseTree?): Node {
        return super.visit(tree)
    }

    override fun visitIfStatement(ctx: tinycParser.IfStatementContext): Node {
        return IfStmt(
            ctx.expr().accept(this) as Expr,
            body(ctx.statement(0)),
            body(ctx.statement(1))
        )
    }

    private fun body(statement: tinycParser.StatementContext?): Body {
        val b = Body(arrayListOf())
        if (statement == null) return b

        val s = statement.accept(this) as Statement
        return if (s is Body) s else b.also { b.statements.add(s) }
    }

    override fun visitWhileStatement(ctx: tinycParser.WhileStatementContext) = WhileStmt(
        ctx.cond.accept(this) as Expr,
        body(ctx.statement()),
        ctx.invariant?.accept(this) as Expr,
        erase= variables(ctx.variant)
    )

    override fun visitBody(ctx: tinycParser.BodyContext) = Body(map(ctx.statement()))

    override fun visitAssignment(ctx: tinycParser.AssignmentContext) = AssignStmt(
        ctx.id().accept(this) as Variable,
        ctx.rhs.accept(this) as Expr,
        type(ctx.type()),

        )

    private fun type(type: tinycParser.TypeContext?): Type? {
        if (type == null) return type;
        return Type(type.t.text, type.a != null)
    }

    override fun visitExpr(ctx: tinycParser.ExprContext): Node {
        if (ctx.primary() != null) return ctx.primary().accept(this)
        return BinaryExpr(
            ctx.expr(0).accept(this) as Expr,
            ctx.op.text,
            ctx.expr(1).accept(this) as Expr
        )
    }

    override fun visitInteger(ctx: tinycParser.IntegerContext) = IntLit(ctx.INT().text.toBigInteger())

    override fun visitFcall(ctx: tinycParser.FcallContext) = FunctionCall(
        ctx.id().text,
        map(ctx.expr())
    )

    override fun visitEmptyStmt(ctx: tinycParser.EmptyStmtContext) = EmptyStmt()
    override fun visitAssert_(ctx: tinycParser.Assert_Context) = AssertStmt(ctx.expr().accept(this) as Expr)
    override fun visitAssume(ctx: tinycParser.AssumeContext) = AssumeStmt(ctx.expr().accept(this) as Expr)
    override fun visitHavoc(ctx: tinycParser.HavocContext) = HavocStmt(
        ctx.args().id().map { it.accept(this) as Variable }.toMutableList()
    )

    override fun visitId(ctx: tinycParser.IdContext) = Variable(ctx.IDENTIFIER().text)
}