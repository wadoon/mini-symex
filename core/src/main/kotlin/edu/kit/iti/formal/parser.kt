package edu.kit.iti.formal

import MiniPascalBaseVisitor
import MiniPascalLexer
import MiniPascalLexer.*
import MiniPascalParser
import TinyCBaseVisitor
import TinyCLexer
import TinyCParser
import edu.kit.iti.formal.QuantifiedExpr.Quantifier.EXISTS
import edu.kit.iti.formal.QuantifiedExpr.Quantifier.FORALL
import org.antlr.v4.runtime.*

object ParsingFacade {
    @JvmStatic
    fun parseProgram(fileName: String): Program {
        val s = CharStreams.fromFileName(fileName)
        return if (fileName.endsWith(".pas"))
            parseProgramPas(s)
        else
            parseProgramC(s)
    }

    @JvmStatic
    fun parseProgramC(stream: CharStream): Program {
        val lexer = TinyCLexer(stream)
        val parser = TinyCParser(CommonTokenStream(lexer))
        val ctx = parser.program()

        require(parser.numberOfSyntaxErrors == 0) {
            "Syntax Errors!"
        }

        return ctx.accept(TinyCAstTranslator()) as Program
    }

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
    fun parseProgramPas(stream: CharStream): Program {
        val (_, ctx) = parseProgramOnly(stream)
        return ctx.accept(PasAstTranslator()) as Program
    }
}


private class PasAstTranslator : MiniPascalBaseVisitor<Node>() {
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
        val p: MutableList<Procedure> = map(ctx.procedure())
        val f: MutableList<Procedure> = map(ctx.function())
        return Program((p + f).toMutableList())
            .withPosition(ctx)
    }

    @Suppress("UNCHECKED_CAST")
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
        val modifies = variables(ctx.spec().modifies)
        val returnType = type(ctx.type())!!

        if (!signature.any { (_, b) -> b.id == "result" }) {
            signature.add(returnType to Variable("result"))
        }

        return Procedure(
            ctx.name.text, signature, args, b,
            requires = ctx.spec().pre?.accept(this) as? Clauses ?: Clauses(),
            ensures = ctx.spec().post?.accept(this) as? Clauses ?: Clauses(),
            modifies = modifies,
            returnType = returnType
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
        erase = variables(ctx.loopSpec().variant),
        label = null
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

    override fun visitParenExpr(ctx: MiniPascalParser.ParenExprContext): Node = ctx.expr().accept(this)

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

    @Suppress("UNCHECKED_CAST")
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
        if (ctx.op.text == "!") UnaryExpr.Operator.NEGATE else UnaryExpr.Operator.SUB,
        ctx.expr().accept(this) as Expr
    ).withPosition(ctx)

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


    override fun visitChoose(ctx: TinyCParser.ChooseContext): Node =
        ChooseStmt(
            ctx.ids().id().map { it.accept(this) as Variable }.toMutableList(),
            ctx.expr().accept(this) as Expr)
            .withPosition(ctx)
}

data class Issue(val from: Int, val to: Int, val message: String)