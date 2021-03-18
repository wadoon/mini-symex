package edu.kit.iti.formal

import MiniPascalBaseVisitor
import MiniPascalLexer
import MiniPascalLexer.*
import MiniPascalParser
import edu.kit.iti.formal.QuantifiedExpr.Quantifier.EXISTS
import edu.kit.iti.formal.QuantifiedExpr.Quantifier.FORALL
import org.antlr.v4.runtime.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
object ParsingFacade {
    @JvmStatic
    fun parseProgramOnly(stream: CharStream): Pair<List<Issue>, MiniPascalParser.ProgramContext> {
        val lexer = MiniPascalLexer(stream)
        val parser = MiniPascalParser(CommonTokenStream(lexer))
        val issues = arrayListOf<Issue>()
        val errorDiagnosticErrorListener = object : BaseErrorListener() {
            override fun syntaxError(
                recognizer: Recognizer<*, *>?,
                offendingSymbol: Any?,
                line: Int,
                charPositionInLine: Int,
                msg: String,
                e: RecognitionException?
            ) {
                val tok = offendingSymbol as Token
                issues.add(Issue(tok.startIndex, tok.stopIndex, msg))
                System.err.println("line $line:$charPositionInLine $msg")
            }
        }
        parser.addErrorListener(errorDiagnosticErrorListener)
        val ctx = parser.program()
        return issues to ctx
    }

    @JvmStatic
    fun parseProgram(stream: CharStream): Program {
        val (_, ctx) = parseProgramOnly(stream)
        return ctx.accept(AstTranslator()) as Program
    }
}

private class AstTranslator : MiniPascalBaseVisitor<Node>() {
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

    override fun visitProgram(ctx: MiniPascalParser.ProgramContext): Node {
        return Program(map(ctx.procedure()))
            .withPosition(ctx)
    }

    private fun <T> map(ctx: List<ParserRuleContext>) =
        ctx.map { it.accept(this) as T }.toMutableList()


    override fun visitQuantifiedExpr(ctx: MiniPascalParser.QuantifiedExprContext): Node =
        QuantifiedExpr(
            binders(ctx.binders()), ctx.expr().accept(this) as Expr,
            if (ctx.q.text.last() == 's') EXISTS else FORALL
        ).withPosition(ctx)


    override fun visitLetExpr(ctx: MiniPascalParser.LetExprContext?): Node {
        TODO()
    }

    override fun visitArrayaccess(ctx: MiniPascalParser.ArrayaccessContext) =
        ArrayAccess(ctx.id().accept(this) as Variable, exprList(ctx.exprList()))
            .withPosition(ctx)


    override fun visitProcedure(ctx: MiniPascalParser.ProcedureContext): Node {
        val b = ctx.body().accept(this) as Body
        val signature = vars(ctx.`var`())
        val args = binders(ctx.a)

        return Procedure(
            ctx.name.text, signature, args, b,
            requires = ctx.spec().pre?.accept(this) as? Clauses ?: Clauses(),
            ensures = ctx.spec().post?.accept(this) as? Clauses ?: Clauses(),
            modifies = variables(ctx.spec().modifies)
        ).withPosition(ctx)
    }

    override fun visitNamedexprs(ctx: MiniPascalParser.NamedexprsContext): Node {
        val clauses = Clauses()
        ctx.namedexpr().forEach {
            val v = it.id()?.accept(this) as Variable?
            val e = it.expr().accept(this) as Expr
            clauses.add(v to e)
        }
        return clauses
    }

    override fun visitFunction(ctx: MiniPascalParser.FunctionContext): Node {
        val b = ctx.body().accept(this) as Body
        val signature = vars(ctx.`var`())
        val args = binders(ctx.a)

        return Procedure(
            ctx.name.text, signature, args, b,
            requires = ctx.spec().pre?.accept(this) as? Clauses ?: Clauses(),
            ensures = ctx.spec().post?.accept(this) as? Clauses ?: Clauses(),
            modifies = variables(ctx.spec().modifies),
            returnType = ctx.type().accept(this) as TypeDecl
        ).withPosition(ctx)
    }

    private fun vars(ctx: MiniPascalParser.VarContext?): MutableList<Pair<TypeDecl, Variable>> =
        if (ctx == null) arrayListOf()
        else {
            val m = arrayListOf<Pair<TypeDecl, Variable>>()
            (ctx.varDecl()).forEach {
                val t = type(it.type()) as TypeDecl
                it.ids().id().forEach { id ->
                    val v = id.accept(this) as Variable
                    m.add(t to v)
                }
            }
            m
        }

    private fun binders(ctx: MiniPascalParser.BindersContext?): MutableList<Pair<TypeDecl, Variable>> =
        if (ctx == null) arrayListOf()
        else {
            (0 until ctx.id().size).map {
                type(ctx.type(it)) as TypeDecl to
                        ctx.id(it).accept(this) as Variable
            }.toMutableList()
        }

    private fun variables(ctx: MiniPascalParser.IdsContext?): MutableList<Variable> =
        if (ctx == null) arrayListOf()
        else ctx.id()?.map { (it.accept(this) as Variable).withPosition(ctx) }?.toMutableList() ?: arrayListOf()

    override fun visitUnary(ctx: MiniPascalParser.UnaryContext) = UnaryExpr(
        if (ctx.op.text == "!") UnaryExpr.Operator.NEGATE else UnaryExpr.Operator.SUB,
        ctx.expr().accept(this) as Expr
    ).withPosition(ctx)

    override fun visitIfStatement(ctx: MiniPascalParser.IfStatementContext): Node {
        return IfStmt(
            ctx.expr().accept(this) as Expr,
            body(ctx.statement(0)),
            body(ctx.statement(1))
        ).withPosition(ctx)

    }

    private fun body(statement: MiniPascalParser.StatementContext?): Body {
        val b = Body(arrayListOf())
        if (statement == null) return b
        b.withPosition(statement)

        val s = statement.accept(this) as Statement
        return if (s is Body) s else b.also { b.statements.add(s) }

    }

    override fun visitWhileStatement(ctx: MiniPascalParser.WhileStatementContext) = WhileStmt(
        ctx.cond.accept(this) as Expr,
        body(ctx.statement()),
        loopInv = ctx.loopSpec().invariant?.accept(this) as Clauses? ?: Clauses(),
        erase = variables(ctx.loopSpec().variant)
    ).withPosition(ctx)

    override fun visitBody(ctx: MiniPascalParser.BodyContext) = Body(map(ctx.statement())).withPosition(ctx)

    override fun visitAssignment(ctx: MiniPascalParser.AssignmentContext) = AssignStmt(
        ctx.id().accept(this) as Variable,
        ctx.rhs?.accept(this) as Expr?,
        null,
    ).withPosition(ctx)

    private fun type(type: MiniPascalParser.TypeContext?): TypeDecl? {
        if (type == null) return null
        return TypeDecl(type.t.text, type.a != null).withPosition(type)
    }

    override fun visitBool(ctx: MiniPascalParser.BoolContext): Node =
        BoolLit(ctx.BOOL_LITERAL().text == "true").withPosition(ctx)

    override fun visitExpr(ctx: MiniPascalParser.ExprContext): Node {
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
            binaryOperator(ctx.op.type),
            ctx.expr(1).accept(this) as Expr
        ).withPosition(ctx)
    }

    private fun binaryOperator(text: Int): BinaryExpr.Operator =
        when (text) {
            PLUS -> BinaryExpr.Operator.ADD
            MINUS -> BinaryExpr.Operator.SUB
            MUL -> BinaryExpr.Operator.MUL
            DIV -> BinaryExpr.Operator.DIV
            MOD -> BinaryExpr.Operator.MOD
            LT -> BinaryExpr.Operator.LT
            LTE -> BinaryExpr.Operator.LTE
            GT -> BinaryExpr.Operator.GT
            GTE -> BinaryExpr.Operator.GTE
            EQUAL -> BinaryExpr.Operator.EQUAL
            NOT_EQUAL -> BinaryExpr.Operator.NOT_EQUAL
            AND -> BinaryExpr.Operator.AND
            OR -> BinaryExpr.Operator.OR
            IMPL -> BinaryExpr.Operator.IMPLIES
            else -> throw IllegalArgumentException("Unknown operator '$text'.")
        }

    override fun visitInteger(ctx: MiniPascalParser.IntegerContext) =
        IntLit(ctx.INT_LITERAL().text.toBigInteger()).withPosition(ctx)

    override fun visitFcall(ctx: MiniPascalParser.FcallContext) = FunctionCall(
        ctx.id().accept(this) as Variable,
        exprList(ctx.exprList())
    ).withPosition(ctx)

    private fun exprList(ctx: MiniPascalParser.ExprListContext): MutableList<Expr> = map(ctx.expr())


    override fun visitEmptyStmt(ctx: MiniPascalParser.EmptyStmtContext) = EmptyStmt().withPosition(ctx)
    override fun visitAssert_(ctx: MiniPascalParser.Assert_Context) =
        AssertStmt(ctx.namedexprs().accept(this) as Clauses).withPosition(ctx)

    override fun visitAssume(ctx: MiniPascalParser.AssumeContext) =
        AssumeStmt(ctx.namedexprs().accept(this) as Clauses).withPosition(ctx)

    override fun visitHavoc(ctx: MiniPascalParser.HavocContext) = HavocStmt(
        ctx.ids().id().map { it.accept(this) as Variable }.toMutableList()
    ).withPosition(ctx)

    override fun visitId(ctx: MiniPascalParser.IdContext) = Variable(ctx.IDENTIFIER().text)
}


data class Issue(val from: Int, val to: Int, val message: String)