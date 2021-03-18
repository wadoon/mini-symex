package edu.kit.iti.formal

import MiniPascalLexer
import SMTLIBv2Lexer
import javafx.geometry.Orientation
import javafx.scene.layout.Priority
import javafx.scene.layout.VBox
import javafx.scene.text.FontPosture
import javafx.stage.FileChooser
import javafx.stage.Popup
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Vocabulary
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.event.MouseOverTextEvent
import org.fxmisc.richtext.model.StyleSpansBuilder
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon
import org.reactfx.EventStreams
import tornadofx.*
import java.io.File
import java.time.Duration
import java.util.*


/**
 *
 * @author Alexander Weigl
 * @version 1 (3/18/21)
 */
fun main(args: Array<String>) {
    launch<MiniSymExUi>(args)
}

class MiniSymExUi : App(MiniSymExView::class, MyStyle::class)

class MiniSymExView : View() {
    private val iconLoad = FontIcon(FontAwesomeRegular.FOLDER_OPEN)
    private val iconSave = FontIcon(FontAwesomeRegular.SAVE)
    private val iconSaveAs = FontIcon(FontAwesomeSolid.SAVE)
    private val iconTranslate = FontIcon(FontAwesomeRegular.PLAY_CIRCLE)

    private val codeEditor = CodeArea()
    private val smtEditor = CodeArea().also { area ->
        val stream = EventStreams.changesOf(area.textProperty())
        stream.successionEnds(Duration.ofMillis(100)) //wait 500ms before responds
            .forgetful()
            .subscribe {
                val text = it.newValue
                val spansBuilder = StyleSpansBuilder<Collection<String>>()
                val lexer = SMTLIBv2Lexer(CharStreams.fromString(text))
                do {
                    val tok = lexer.nextToken()
                    if (tok.type == -1) break
                    val typ = translateSmtLibToStyleNames(tok.type, lexer.vocabulary)
                    spansBuilder.add(Collections.singleton(typ), tok.text.length)
                } while (tok.type != -1)
                try {
                    area.setStyleSpans(0, spansBuilder.create())
                } catch (ignore: IndexOutOfBoundsException) {
                    //ignore
                }
            }
    }


    private val fileChooser by lazy { FileChooser() }

    private var lastOpenedFile: File? = null

    override val root = vbox {
        toolbar(
            button("Load", iconLoad) {
                action {
                    fileChooser.showOpenDialog(currentWindow)?.let { file ->
                        val text = file.readText()
                        codeEditor.replaceText(text)
                        this@MiniSymExView.lastOpenedFile = file
                        this@MiniSymExView.title = file.absolutePath
                    }
                }
            },
            button("Save", iconSave) {
                action {
                    save(lastOpenedFile)
                }
            },
            button("Save As", iconSaveAs) {
                action { save(null) }
            },
            separator(),
            button("Translate", iconTranslate) {
                action {
                    val program = ParsingFacade.parseProgram(CharStreams.fromString(codeEditor.text, "<source>"))
                    val symEx = SymEx2(program.procedures)
                    val main = program.procedures.find { it.name == "main" }
                    if (main != null) {
                        symEx.proveBody(main)
                        val buffer = StringBuilder()
                        var indent = 0
                        symEx.commands.joinTo(buffer, "\n") {
                            val t = ("    " * indent) + it
                            if (it.startsWith("(pop"))
                                indent -= 1
                            if (it.startsWith("(push"))
                                indent += 1
                            t
                        }
                        smtEditor.replaceText(buffer.toString())
                    }
                }
            },
        )
        splitpane(Orientation.HORIZONTAL, codeEditor, smtEditor) {
            VBox.setVgrow(this, Priority.ALWAYS)
        }
    }

    private fun save(path: File? = null) {
        val file = path ?: fileChooser.showSaveDialog(currentWindow)
        if (file != null) {
            val text = codeEditor.text
            file.writeText(text)
            lastOpenedFile = file
            title = file.absolutePath
        }
    }

    init {
        codeEditor.paragraphGraphicFactory = LineNumberFactory.get(codeEditor)
        //editor. = true


        val stream = EventStreams.changesOf(codeEditor.textProperty())
        stream.successionEnds(Duration.ofMillis(100)) //wait 500ms before responds
            .forgetful()
            .subscribe { reHighlight() }

        stream.successionEnds(Duration.ofMillis(500)) //wait 500ms before responds
            .forgetful()
            .subscribe {
                val text = codeEditor.text
                val (p, _) = ParsingFacade.parseProgramOnly(CharStreams.fromString(text))
                issues.clear()
                issues.addAll(p)
                reHighlight()
            }


        val popupMsg = label {
            style {
                backgroundColor += c("black")
                textFill = c("white")
                paddingAll = 5.0
            }
        }

        val popup = Popup()
        popup.content.add(popupMsg)
        codeEditor.mouseOverTextDelay = Duration.ofSeconds(1)
        codeEditor.addEventHandler(MouseOverTextEvent.MOUSE_OVER_TEXT_BEGIN) { e ->
            val chIdx = e.characterIndex
            val pos = e.screenPosition
            val issue = issues.find { it.from <= chIdx && chIdx <= it.to }
            issue?.let {
                popupMsg.text = it.message
                popup.show(codeEditor, pos.x, pos.y + 10)
            }
        }
        codeEditor.addEventHandler(MouseOverTextEvent.MOUSE_OVER_TEXT_END) { popup.hide() }


    }

    private val issues = arrayListOf<Issue>()
    private fun reHighlight() {
        val text = codeEditor.text
        val spansBuilder = StyleSpansBuilder<Collection<String>>()
        val lexer = MiniPascalLexer(CharStreams.fromString(text))
        do {
            val tok = lexer.nextToken()
            if (tok.type == -1) break
            val typ = translatePascalToStyleNames(tok.type)
            spansBuilder.add(Collections.singleton(typ), tok.text.length)
        } while (tok.type != -1)
        try {
            codeEditor.setStyleSpans(0, spansBuilder.create())
        } catch (ignore: IndexOutOfBoundsException) {
            //ignore
        }
        try {
            issues.forEach {
                codeEditor.setStyle(it.from, it.to + 1, Collections.singleton("error"))
            }
        } catch (ignore: IndexOutOfBoundsException) {
            //ignore
        }
    }
}

private operator fun String.times(indent: Int): String = (1..indent).joinToString("") { this }


class MyStyle : Stylesheet() {
    companion object {
        val styledTextArea by cssclass("styled-text-area")
        val text by cssclass()
        val literal by cssclass()
        val keyword by cssclass()
        val verification_keyword by cssclass()
        val operator by cssclass()
        val comment by cssclass()
        val error by cssclass()
    }

    init {
        styledTextArea {
            text {
                backgroundColor += c("yellow")
            }
        }

        literal {
            fill = c("lightblue")
        }

        keyword {
            fill = c("blue")
            underline = true
        }

        verification_keyword {
            underline = true
            fontStyle = FontPosture.ITALIC
            fill = c("green")
        }

        operator {
        }

        comment {
            fill = c("gray")
            fontStyle = FontPosture.ITALIC
        }

        error {
            fill = c("red")
            fontStyle = FontPosture.ITALIC
            underline = true
        }
    }
}

private fun translatePascalToStyleNames(type: Int): String = when (type) {
    MiniPascalLexer.BOOL_LITERAL,
    MiniPascalLexer.INT_LITERAL,
    MiniPascalLexer.STRING_LITERAL ->
        "literal"
    MiniPascalLexer.PROCEDURE,
    MiniPascalLexer.FUNCTION,
    MiniPascalLexer.VAR,
    MiniPascalLexer.WHILE,
    MiniPascalLexer.IF,
    MiniPascalLexer.ARRAY,
    MiniPascalLexer.OF,
    MiniPascalLexer.DO,
    MiniPascalLexer.INT,
    MiniPascalLexer.BOOL,
    MiniPascalLexer.THEN,
    MiniPascalLexer.ELSE,
    MiniPascalLexer.FORALL,
    MiniPascalLexer.EXISTS,
    MiniPascalLexer.BEGIN,
    MiniPascalLexer.END ->
        "keyword"

    MiniPascalLexer.POST,
    MiniPascalLexer.PRE,
    MiniPascalLexer.MODIFIES,
    MiniPascalLexer.VARIANT,
    MiniPascalLexer.INVARIANT,
    MiniPascalLexer.HAVOC,
    MiniPascalLexer.ASSUME,
    MiniPascalLexer.ASSERT ->
        "verification_keyword"

    MiniPascalLexer.COLON,
    MiniPascalLexer.SEMI,
    MiniPascalLexer.AND,
    MiniPascalLexer.OR,
    MiniPascalLexer.XOR,
    MiniPascalLexer.IMPL,
    MiniPascalLexer.PLUS,
    MiniPascalLexer.MINUS,
    MiniPascalLexer.DIV,
    MiniPascalLexer.MOD,
    MiniPascalLexer.MUL,
    MiniPascalLexer.GT,
    MiniPascalLexer.LT,
    MiniPascalLexer.GTE,
    MiniPascalLexer.LTE,
    MiniPascalLexer.EQUAL,
    MiniPascalLexer.NOT_EQUAL,
    MiniPascalLexer.ASSIGN,
    MiniPascalLexer.LPAREN,
    MiniPascalLexer.RPAREN,
    MiniPascalLexer.RBRACKET,
    MiniPascalLexer.LBRACKET ->
        "operator"
    MiniPascalLexer.BLOCK_COMMENT,
    MiniPascalLexer.LINE_COMMENT ->
        "comment"
    else -> "empty"
}

private fun translateSmtLibToStyleNames(type: Int, vok: Vocabulary): String {
    val name = vok.getSymbolicName(type)
    return when {
        name.startsWith("CMD") -> "verification_keyword"
        name.startsWith("PS") -> "keyword"
        name.startsWith("GRW") -> "keyword"
        name.startsWith("PK") -> "operator"
        type == SMTLIBv2Lexer.Comment -> "comment"
                type == SMTLIBv2Lexer.Numeral ||
                type == SMTLIBv2Lexer.Binary ||
                type == SMTLIBv2Lexer.String ||
                type == SMTLIBv2Lexer.HexDecimal ->
            "literal"
        else -> "empty"
    }
}