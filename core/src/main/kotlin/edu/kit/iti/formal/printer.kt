package edu.kit.iti.formal

class Printer() : Visitor<String> {
    override fun visit(n: Program): String =
        n.procedures.joinToString("\n\n") { it.accept(this) }

    override fun visit(n: BinaryExpr): String = n.toHuman()

    override fun visit(n: UnaryExpr): String = n.toHuman()

    override fun visit(n: Variable): String = n.toHuman()

    override fun visit(n: WhileStmt): String =
        """
            while (${n.cond.accept(this)}) {
                ${n.body.accept(this)}
            }
        """.trimIndent()

    override fun visit(n: IfStmt): String =
        """if(${n.cond.accept(this)}) 
${n.then.accept(this)}
else 
${n.otherwise?.accept(this) ?: ""}  
        """

    override fun visit(n: AssertStmt): String = "assert ${n.cond.accept(this)};"
    override fun visit(n: AssumeStmt): String = "assume ${n.cond.accept(this)};"
    override fun visit(n: HavocStmt): String = "havoc ${n.ids.joinToString(", ") { it.accept(this) }}"
    override fun visit(n: AssignStmt): String =
        (n.decl?.accept(this)?.let { "$it " } ?: "") + n.id.accept(this) +
                (n.arrayAccess?.let{ "[" + it.accept(this) + "]"}?: "") +
                (n.rhs?.let { " = " + it.accept(this) } ?: "") + ";"

    override fun visit(n: TypeDecl): String = n.name + (if (n.array) "[]" else "")
    override fun visit(n: Procedure): String =
        """${n.returnType.accept(this)} ${n.name} (${
            n.args.joinToString(", ") { (a, b) ->
                a.accept(this) + " " + b.accept(
                    this
                )
            }
        })
                ${n.body.accept(this)}            
        """.trimIndent()

    override fun visit(n: IntLit): String = n.toHuman()
    override fun visit(n: QuantifiedExpr) = n.toHuman()
    override fun visit(n: BoolLit): String = n.toHuman()
    override fun visit(n: ArrayAccess): String = n.toHuman()
    override fun visit(n: Clauses): String = n.joinToString(", ") { (a, b) -> b.toHuman() }

    override fun visit(n: Body): String =
        "{\n" + n.statements.joinToString("\n") { "    " + it.accept(this).replace("\n", "\n    ") } + "\n}"

    override fun visit(n: EmptyStmt): String = ";"
    override fun visit(n: FunctionCall): String =
        "${n.id.accept(this)}(${n.args.joinToString(", ") { it.accept(this) }})"

    override fun visit(n: ChooseStmt): String = "choose ${n.variable.accept(this)} : ${n.expr.accept(this)};"
}