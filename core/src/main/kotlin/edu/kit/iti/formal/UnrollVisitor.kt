package edu.kit.iti.formal

open class MutableVisitor() : Visitor<Unit> {
    override fun visit(n: Program) {
        n.procedures.forEach { it.accept(this) }
    }

    override fun visit(n: BinaryExpr) {
        n.left.accept(this)
        n.right.accept(this)
    }

    override fun visit(n: UnaryExpr) {
        n.right.accept(this)
    }

    override fun visit(n: Variable) {}

    override fun visit(n: WhileStmt) {
        n.cond.accept(this)
        n.body.accept(this)
        n.erase.forEach { it.accept(this) }
        n.loopInv.forEach { (_, it) -> it.accept(this) }
    }

    override fun visit(n: IfStmt) {
        n.cond.accept(this)
        n.then.accept(this)
        n.otherwise?.accept(this)
    }

    override fun visit(n: AssertStmt) {
        n.cond.accept(this)
    }

    override fun visit(n: AssumeStmt) {
        n.cond.accept(this)
    }

    override fun visit(n: HavocStmt) {
        n.ids.forEach { it.accept(this) }
    }

    override fun visit(n: AssignStmt) {
        n.decl?.accept(this)
        n.id.accept(this)
        n.arrayAccess?.accept(this)
        n.rhs?.accept(this)
    }

    override fun visit(n: TypeDecl) {}

    override fun visit(n: Procedure) {
        n.signature.forEach { (a, b) -> a.accept(this); b.accept(this) }
        n.args.forEach { (a, b) -> a.accept(this); b.accept(this) }
        n.ensures.accept(this)
        n.requires.accept(this)
        n.returnType.accept(this)
        n.modifies.forEach { it.accept(this) }
        n.body.accept(this)
    }

    override fun visit(n: IntLit) {}

    override fun visit(n: QuantifiedExpr) {
        n.binders.forEach { (a, b) -> a.accept(this); b.accept(this) }
        n.sub.accept(this)
    }

    override fun visit(n: BoolLit) {}

    override fun visit(n: ArrayAccess) {
        n.id.accept(this)
        n.args.forEach { it.accept(this) }
    }

    override fun visit(n: Clauses) {
        n.forEach { (_, it) -> it.accept(this) }
    }

    override fun visit(n: Body) {
        n.statements.forEach { it.accept(this) }
    }

    override fun visit(n: EmptyStmt) {}

    override fun visit(n: FunctionCall) {
        n.id.accept(this)
        n.args.forEach { it.accept(this) }
    }

    override fun visit(n: ChooseStmt) {
        n.variables.forEach { it.accept(this) }
        n.expr.accept(this)
    }

    override fun visit(typeCast: TypeCast) {
        TODO("Not yet implemented")
    }

    override fun visit(lit: DoubleLit) {
        TODO("Not yet implemented")
    }

    override fun visit(pcall: ProcedureCall) {
        TODO("Not yet implemented")
    }

    override fun visit(arrayInit: ArrayInit) {
        TODO("Not yet implemented")
    }

    override fun visit(returnStmt: ReturnStmt) {
        TODO("Not yet implemented")
    }
}


class UnrollVisitor(val unroll: Map<String, Int>) : MutableVisitor() {
    override fun visit(n: Body) {
        val newStatements = arrayListOf<Statement>()
        n.statements.forEach {
            it.accept(this) // expand children

            if (it is WhileStmt && it.label in unroll) {
                newStatements.addAll(
                    unroll(it, unroll[it.label]!!)
                )
            } else {
                newStatements.add(it)
            }
        }
        n.statements.clear()
        n.statements.addAll(newStatements)
    }

    private fun unroll(whileStmt: WhileStmt, k: Int): Collection<Statement> {
        require(k > 0)
        fun recur(a: Int): Statement =
            if (a == 0) EmptyStmt()
            else IfStmt(whileStmt.cond,
                Body().also {
                    it.statements.addAll(whileStmt.body.statements);
                    it.statements.add(recur(a - 1))
                })
        return arrayListOf(recur(k))
    }

    private fun unrollLinear(loop: WhileStmt, k: Int): List<Statement> {
        //TODO
        val statements = arrayListOf<Statement>()
        require(k > 0)
        for (i in 1 until k) {
            statements += IfStmt(loop.cond, loop.body)
        }
        val ass = AssertStmt(Clauses())
        statements += ass
        ass.cond.add(null to UnaryExpr(UnaryExpr.Operator.NEGATE, loop.cond))
        return statements
    }
}
