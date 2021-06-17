package edu.kit.iti.formal

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import org.antlr.v4.runtime.CharStreams
import java.io.PrintWriter

class MiniSymEx : CliktCommand() {
    private val inputFile by argument("FILE", help = "While-program").file()
    private val printNames by option("-n", help = "print the position infos", metavar = "PROCEDURE")
        .flag("-N", default = true)
    private val entryPoint by option("--main", help = "print the position infos").default("main")

    private val unrollings by option("-r", "--unroll")
        .associate(":")

    private val unrollings0 by lazy {
        unrollings.map { (k, v) -> k to v.toInt() }.toMap()
    }


    private val output by option("-o", "--output", help = "a file destination to write SMT to", metavar = "SMT").file(
        mustBeWritable = true
    )

    override fun run() {
        PRINT_ATTRIBUTES = printNames

        val program = parseProgram(inputFile.absolutePath)

        val entryProgram = program.procedures.find { it.name == entryPoint }

        require(entryProgram != null) { "Program $entryPoint not found" }

        if (unrollings0.isNotEmpty()) {
            unrollLoops(unrollings0, program)
        }

        val symEx = SymEx2()
        symEx.proveBody(entryProgram)
        val writer = output?.let { PrintWriter(it) } ?: PrintWriter(System.out)
        writer.use {
            symEx.encodeInto(it)
        }
    }

    private fun unrollLoops(unrollings0: Map<String, Int>, program: Program) {
        program.accept(UnrollVisitor(unrollings0))
        println(program.accept(Printer()))
    }

    private fun parseProgram(fileName: String): Program {
        val s = CharStreams.fromFileName(fileName)
        return if (fileName.endsWith(".pas"))
            PasParsingFacade.parseProgram(s)
        else
            CParsingFacade.parseProgram(s)
    }
}

fun main(args: Array<String>) = MiniSymEx().main(args)