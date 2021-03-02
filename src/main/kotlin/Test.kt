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
        val symEx = SymEx()
        symEx.executeStatement(program.procedures.first().body, State())
    }
}