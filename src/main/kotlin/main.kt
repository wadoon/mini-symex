import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import org.antlr.v4.runtime.CharStreams

class MiniSymEx : CliktCommand() {
    val inputFile by argument("FILE", help = "While-program").file()
    val printNames by option("-n", help = "print the position infos", metavar = "PROCEDURE")
        .flag("-N", default = true)
    val entryPoint by option("--main", help = "print the position infos").default("main")

    override fun run() {
        PRINT_ATTRIBUTES = printNames

        val program = ParsingFacade.parseProgram(
            CharStreams.fromFileName(inputFile.absolutePath)
        )

        val entryProgram = program.procedures.find { it.name == entryPoint }

        require(entryProgram != null) { "Program $entryPoint not found" }

        val symEx = SymEx()

        val proofObligation = Body(arrayListOf())
        proofObligation.statements.add(AssumeStmt(entryProgram.requires))
        proofObligation.statements.add(entryProgram.body)
        proofObligation.statements.add(AssertStmt(entryProgram.ensures))
        symEx.executeStatement(proofObligation, State())
    }
}

fun main(args: Array<String>) = MiniSymEx().main(args)