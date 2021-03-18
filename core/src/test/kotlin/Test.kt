import edu.kit.iti.formal.ParsingFacade
import edu.kit.iti.formal.SymEx2
import org.antlr.v4.runtime.CharStreams

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/25/21)
 */
object Test {
    @JvmStatic
    fun main(args: Array<String>) {
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
        """.trimIndent();

        val program = ParsingFacade.parseProgram(CharStreams.fromString(p))
        val symEx = SymEx2()
        symEx.executeStatement(program.procedures.first().body)
    }
}