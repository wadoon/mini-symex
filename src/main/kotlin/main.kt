import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import org.antlr.v4.runtime.CharStreams
import java.io.PrintWriter

class MiniSymEx : CliktCommand() {
    val inputFile by argument("FILE", help = "While-program").file()
    val printNames by option("-n", help = "print the position infos", metavar = "PROCEDURE")
        .flag("-N", default = true)
    val entryPoint by option("--main", help = "print the position infos").default("main")

    val output by option("-o", "--output", help = "a file destination to write SMT to", metavar = "SMT").file(
        mustBeWritable = true
    )

    override fun run() {
        PRINT_ATTRIBUTES = printNames

        val program = ParsingFacade.parseProgram(
            CharStreams.fromFileName(inputFile.absolutePath)
        )

        val entryProgram = program.procedures.find { it.name == entryPoint }

        require(entryProgram != null) { "Program $entryPoint not found" }

        val symEx = SymEx2()
        symEx.proveBody(entryProgram)
        val writer = output?.let { PrintWriter(it) } ?: PrintWriter(System.out)
        writer.use {
            symEx.encodeInto(it)
        }
    }
}

fun main(args: Array<String>) = MiniSymEx().main(args)