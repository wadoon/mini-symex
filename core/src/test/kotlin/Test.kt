import edu.kit.iti.formal.MiniSymEx
import edu.kit.iti.formal.ParsingFacade
import edu.kit.iti.formal.SymEx2
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestFactory
import java.io.File
import java.io.FilenameFilter
import java.util.*
import java.util.stream.Stream

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
object Test {
    @TestFactory
    fun testAllExamples(): Stream<DynamicTest> =
        Arrays.stream(File("../examples").listFiles(PasFilter)).map { s->
            DynamicTest.dynamicTest(s.name) {
                parseAndLoad(s)
            }
        }

    private fun parseAndLoad(s: File) {
        val program = ParsingFacade.parseProgram(s.absolutePath)
        val symEx = SymEx2()
        val b = program.procedures.first()
        symEx.proveBody(b)
    }

    @Test
    fun testAngel() {
        MiniSymEx().main(arrayListOf("../examples/Angels.c"))
    }

    @Test
    fun main() {
        val p = """
void main() {
    int a = 1;
    int b = 0;
    havoc b;
    assert a == 1;
    if(b == 0) {
        a = a+2;
    } else {
        a = a+4;
    }          
    assert a != 1;
}
        """.trimIndent()

        val program = ParsingFacade.parseProgramC(CharStreams.fromString(p))
        val symEx = SymEx2()
        symEx.executeStatement(program.procedures.first().body)
    }
}

object PasFilter : FilenameFilter {
    override fun accept(dir: File?, name: String)=name.endsWith("pas")
}
