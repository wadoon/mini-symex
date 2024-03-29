package edu.kit.iti.formal

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.associate
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import java.io.PrintWriter

class MiniSymEx : CliktCommand() {
    private val useWPEngine by option("-wp", help = "weakest precondition engine").flag()

    private val inputFile by argument("FILE", help = "While-program").file()
    private val printNames by option("-n", help = "print the position infos", metavar = "PROCEDURE")
        .flag("-N", default = false)
    private val entryPoint by option("--main", help = "name of the entry point (verification subject)").default("main")

    private val unrollings by option("-r", "--unroll").associate(":")

    private val unrollings0 by lazy {
        unrollings.map { (k, v) -> k to v.toInt() }.toMap()
    }


    private val output by option("-o", "--output", help = "a file destination to write SMT to", metavar = "SMT").file(
        mustBeWritable = true
    )

    override fun run() {
        PRINT_ATTRIBUTES = printNames

        val program = ParsingFacade.parseProgram(inputFile.absolutePath)

        val entryProgram = program.procedures.find { it.name == entryPoint }

        require(entryProgram != null) { "Program $entryPoint not found" }


        if (unrollings0.isNotEmpty()) {
            unrollLoops(unrollings0, program)
        }

        if (useWPEngine) {
            val symEx = WP(program.procedures)
            val state = WP.Scope()
            val result = symEx.executeStatements(entryProgram.body.statements, state)
            val writer = output?.let { PrintWriter(it) } ?: PrintWriter(System.out)
            writer.use {
                state.signature.forEach{(v,t)->
                    it.println("(declare-const ${v.toHuman()} ${t.toSmtType()})")
                }
                it.println("(assert (not $result))")
                it.println("(check-sat)")
                it.println("(get-model)")
            }
        } else {
            val symEx = SymEx2(program.procedures)
            val state = symEx.Scope()
            program.globalVariables.forEach {
                symEx.executeStatement(it, state)
            }
            state.makeAllKnownVariablesGlobal()
            symEx.proveBody(entryProgram, state)
            val writer = output?.let { PrintWriter(it) } ?: PrintWriter(System.out)
            writer.use {
                symEx.encodeInto(it)
            }
        }
    }

    private fun unrollLoops(unrollings0: Map<String, Int>, program: Program) {
        program.accept(UnrollVisitor(unrollings0))
        println(program.accept(Printer()))
    }
}

fun main(args: Array<String>) = MiniSymEx().main(args)


