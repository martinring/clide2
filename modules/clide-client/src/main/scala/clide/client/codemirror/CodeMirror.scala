package clide.client.codemirror

import org.scalajs.dom.{ Event, HTMLElement, HTMLTextAreaElement }
import scala.scalajs.js
import scala.scalajs.js.annotation.JSName
import scala.scalajs.js.annotation.JSExport
import scala.scalajs.js.annotation.JSExportDescendentObjects
import scala.scalajs.js.RegExp
import scala.scalajs.js.UndefOr

@JSName("CodeMirror")
object CodeMirror extends js.Object with WithEvents {
  def version: String = ???
  def fromTextArea(host: HTMLTextAreaElement, options: CodeMirrorConfiguration = ???): CodeMirror with FromTextArea = ???
  def defaults: CodeMirrorConfiguration = ???
  def defineExtension(name: String, value: js.Any): Unit = ???
  def defineDocExtension(name: String, value: js.Any): Unit = ???
  def defineOption(name: String, default: js.Any, updateFunc: js.Function): Unit = ???
  def defineInitHook(func: js.Function1[CodeMirror,Unit]): Unit = ???
  def registerHelper(typ: String, name: String, value: js.Any): Unit = ???
  def registerGlobalHelper(typ: String, name: String, predicate: js.Function2[String,CodeMirror,Boolean], value: js.Any): Unit = ???  
  def Pos(line: Int, ch: Int = ???): Position = ???
  def changeEnd(change: js.Any): Position = ???
  def copyState[S](mode: Mode[S], state: S): S = ???

  def Pass: Nothing = ???
  def defineMode[S](name: String, constructor: js.Function2[CodeMirrorConfiguration, Any, Mode[S]]): Unit = ???
  def defineMIME(mime: String, modeSpec: String): Unit = ???
  def defineMIME[S](mime: String, modeSpec: Mode[S]): Unit = ???
  def extendMode[S](mode: String, extensions: Mode[S]): Unit = ???
}

trait FromTextArea {
  def save(): Unit = ???
  def toTextArea(): Unit = ???
  def getTextArea(): HTMLTextAreaElement = ???
}

@JSName("CodeMirror")
class CodeMirror protected () extends WithEvents {
  def this(place: HTMLElement, options: CodeMirrorConfiguration = ???) = this()
  def this(place: js.Function1[HTMLElement, Unit], options: CodeMirrorConfiguration = ???) = this()
  def hasFocus(): Boolean = ???
  def findPosH(start: Position, amount: Int, unit: String, visually: Boolean): PositionWithHitSide = ???
  def findPosV(start: Position, amound: Int, unit: String): PositionWithHitSide = ???
  def findWordAt(pos: Position): Range = ???
  
  def setOption(option: String, value: js.Any): Unit = ???
  def getOption(option: String): js.Dynamic = ???
  def addKeyMap(map: js.Any, bottom: Boolean = ???): Unit = ???
  def removeKeyMap(map: js.Any): Unit = ???
  def addOverlay(mode: String, options: js.Any = ???): Unit = ???
  def addOverlay[S](mode: Mode[S], options: js.Any = ???): Unit = ???
  def removeOverlay(mode: String): Unit = ???
  def removeOverlay[S](mode: Mode[S]): Unit = ???  
  
  def getDoc(): Doc = ???
  def swapDoc(doc: Doc): Doc = ???
  def setGutterMarker(line: Int, gutterID: String, value: HTMLElement): LineHandle = ???
  def setGutterMarker(line: LineHandle, gutterID: String, value: HTMLElement): LineHandle = ???  
  def clearGutter(gutterID: String): Unit = ???
  def addLineClass(line: Int, where: String, _clazz: String): LineHandle = ???
  def addLineClass(line: LineHandle, where: String, _clazz: String): LineHandle = ???
  def removeLineClass(line: Int, where: String, clazz: String): LineHandle = ???
  def removeLineClass(line: LineHandle, where: String, clazz: String): LineHandle = ???
  def lineInfo(line: Int): js.Any = ???
  def lineInfo(line: LineHandle): js.Any = ???
  def addWidget(pos: Position, node: HTMLElement, scrollIntoView: Boolean = ???): Unit = ???
  def addLineWidget(line: Int, node: HTMLElement, options: js.Any = ???): LineWidget = ???
  def addLineWidget(line: LineHandle, node: HTMLElement, options: js.Any = ???): LineWidget = ???
  def setSize(width: Int, height: js.Any): Unit = ???
  def setSize(width: String, height: js.Any): Unit = ???
  def scrollTo(x: Int, y: Int): Unit = ???
  def getScrollInfo(): js.Any = ???
  def scrollIntoView(pos: Position, margin: Int = ???): Unit = ???
  def cursorCoords(where: Boolean, mode: String): js.Any = ???
  def charCoords(pos: Position, mode: String): js.Any = ???
  def coordsChar(`object`: js.Any, mode: String = ???): Position = ???
  def defaultTextHeight(): Int = ???
  def defaultCharWidth(): Int = ???
  def getViewport(): js.Any = ???
  def refresh(): Unit = ???
  def getTokenAt(pos: Position): js.Any = ???
  def getStateAfter(line: Int = ???): js.Dynamic = ???
  def operation[T](fn: js.Function0[T]): T = ???
  def indentLine(line: Int, dir: String = ???): Unit = ???
  def focus(): Unit = ???
  def getInputField(): HTMLTextAreaElement = ???
  def getWrapperElement(): HTMLElement = ???
  def getScrollerElement(): HTMLElement = ???
  def getGutterElement(): HTMLElement = ???
}

trait DocEditorCommon extends js.Object {
  /** Get the current editor content. You can pass it an optional argument to specify the string to be used to separate lines (defaults to "\n"). */
  def getValue(separator: String = ???): String = ???
  /** Set the editor content */
  def setValue(content: String): Unit = ???
  /** Get the text between the given points in the editor, which should be {line, ch} objects. An optional third argument can be given to indicate the line separator string to use (defaults to "\n"). */
  def getRange(from: Position, to: Position, separator: String = ???): String = ???
  /** Replace the part of the document between from and to with the given string. from and to must be {line, ch} objects. to can be left off to simply insert the string at position from. When origin is given, it will be passed on to "change" events, and its first letter will be used to determine whether this change can be merged with previous history events, in the way described for selection origins. */
  def replaceRange(replacement: String, from: Position, to: Position, origin: String = ???): Unit = ???
  /** Get the content of line n. */
  def getLine(n: Int): String = ???
  /** Get the number of lines in the editor. */
  def lineCount(): Int = ???
  /** Get the first line of the editor. This will usually be zero but for linked sub-views, or documents instantiated with a non-zero first line, it might return other values. */
  def firstLine(): Int = ???
  /** Get the last line of the editor. This will usually be doc.lineCount() - 1, but for linked sub-views, it might return other values. */  
  def lastLine(): Int = ???
  /** Fetches the line handle for the given line number. */
  def getLineHandle(num: Int): LineHandle = ???
  /** Given a line handle, returns the current position of that line (or null when it is no longer in the document). */
  def getLineNumber(handle: LineHandle): Int = ???
  /** Iterate over the whole document, or if start and end line numbers are given, the range from start up to (not including) end, and call f for each line, passing the line handle. This is a faster way to visit a range of line handlers than calling getLineHandle for each of them. Note that line handles have a text property containing the line's content (as a string). */
  def eachLine(f: js.Function1[LineHandle, Unit]): Unit = ???
  /** Iterate over the whole document, or if start and end line numbers are given, the range from start up to (not including) end, and call f for each line, passing the line handle. This is a faster way to visit a range of line handlers than calling getLineHandle for each of them. Note that line handles have a text property containing the line's content (as a string). */  
  def eachLine(start: Int, end: Int, f: js.Function1[LineHandle, Unit]): Unit = ???
  /** Set the editor content as 'clean', a flag that it will retain until it is edited, and which will be set again when such an edit is undone again. Useful to track whether the content needs to be saved. This function is deprecated in favor of changeGeneration, which allows multiple subsystems to track different notions of cleanness without interfering. */
  def markClean(): Unit = ???
  /** Returns a number that can later be passed to isClean to test whether any edits were made (and not undone) in the meantime. If closeEvent is true, the current history event will be ‘closed’, meaning it can't be combined with further changes (rapid typing or deleting events are typically combined). */
  def changeGeneration(closeEvent: Boolean = ???): Int = ???
  /** Returns whether the document is currently clean — not modified since initialization or the last call to markClean if no argument is passed, or since the matching call to changeGeneration if a generation value is given. */
  def isClean(generation: Int = ???): Boolean = ???
  /** Get the currently selected code. Optionally pass a line separator to put between the lines in the output. When multiple selections are present, they are concatenated with instances of lineSep in between. */
  def getSelection(lineSep: String = ???): String = ???
  /** Returns an array containing a string for each selection, representing the content of the selections. */
  def getSelections(lineSep: String = ???): String = ???
  /** Replace the selection(s) with the given string. By default, the new selection ends up after the inserted text. The optional select argument can be used to change this—passing "around" will cause the new text to be selected, passing "start" will collapse the selection to the start of the inserted text. */
  def replaceSelection(replacement: String, select: String = ???): Unit = ???
  /** Retrieve one end of the primary selection. start is a an optional string indicating which end of the selection to return. It may be "from", "to", "head" (the side of the selection that moves when you press shift+arrow), or "anchor" (the fixed side of the selection). Omitting the argument is the same as passing "head". A {line, ch} object will be returned. */
  def getCursor(start: String = ???): Position = ???
  /** Retrieves a list of all current selections. These will always be sorted, and never overlap (overlapping selections are merged). Each object in the array contains anchor and head properties referring to {line, ch} objects. */ 
  def listSelections(): js.Array[Range] = ???
  /** Return true if any text is selected */
  def somethingSelected(): Boolean = ???
  def setCursor(pos: Position, ch: Int = ???, options: SelectionOptions = ???): Unit = ???
  def setCursor(pos: Int, ch: Int = ???, options: SelectionOptions = ???): Unit = ???
  def setSelection(anchor: Position, head: Position = ???, options: SelectionOptions = ???): Unit = ???
  def setSelections(ranges: js.Array[Range], primary: Int = ???, options: SelectionOptions = ???): Unit = ???
  def addSelection(anchor: Position, head: Position = ???): Unit = ???
  def extendSelection(from: Position, to: Position = ???, options: SelectionOptions = ???): Unit = ???
  def extendSelections(heads: js.Array[Position], options: SelectionOptions = ???): Unit = ???
  def extendSelectionsBy(f: js.Function1[Range,Range], options: SelectionOptions = ???): Unit = ???
  def setExtending(value: Boolean): Unit = ???
  def getExtending(): Boolean = ???
  def undo(): Unit = ???
  def redo(): Unit = ???
  def undoSelection(): Unit = ???
  def redoSelection(): Unit = ???
  def historySize(): HistorySizeInfo = ???
  def clearHistory(): Unit = ???
  def getHistory(): js.Any = ???
  def setHistory(history: js.Any): Unit = ???
  
  def markText(from: Position, to: Position, options: TextMarkerOptions = ???): TextMarker = ???
  def setBookmark(pos: Position, options: TextMarkerOptions = ???): TextMarker = ???
  def findMarks(from: Position, to: Position): js.Array[TextMarker] = ???
  def findMarksAt(pos: Position): js.Array[TextMarker] = ???
  def getAllMarks(): js.Array[TextMarker] = ???
  
  
}

trait HistorySizeInfo extends js.Object {
  val undo: Int = ???
  val redo: Int = ???
}

trait SelectionOptions extends js.Object {
  /**
   * Determines whether the selection head should be scrolled into view. Defaults to true.
   */
  var scroll: Boolean = ???
  /**
   * Detemines whether the selection history event may be merged with the previous one. When an origin starts with the character +, and the last recorded selection had the same origin and was similar (close in time, both collapsed or both non-collapsed), the new one will replace the old one. When it starts with *, it will always replace the previous event (if that had the same origin). Built-in motion uses the "+move" origin.
   */
  var origin: String = ???
  /**
   * Determine the direction into which the selection endpoints should be adjusted when they fall inside an atomic range. Can be either -1 (backward) or 1 (forward). When not given, the bias will be based on the relative position of the old selection—the editor will try to move further away from that, to prevent getting stuck.
   */
  var bias: Int = ???  
}

trait WithEvents extends js.Object {
  def on(eventName: String, handler: js.Function1[CodeMirror, Unit]): Unit = ???
  def off(eventName: String, handler: js.Function1[CodeMirror, Unit]): Unit = ???
}

@JSName("Doc")
class Doc protected () extends DocEditorCommon with WithEvents {
  def this(text: String, mode: js.Any = ???, firstLineNumber: Int = ???) = this()
  def getEditor(): CodeMirror
  def copy(copyHistory: Boolean = ???): Doc = ???
  
}

trait Range extends js.Object {
  var anchor: Position = ???
  var head: Position = ???
}

trait Coordinates extends js.Object {
  var left: Int
  var top: Int
}

trait LineHandle extends WithEvents {
  def text: String = ???
}

trait TextMarker extends WithEvents {
  def clear(): Unit = ???
  def find(): Position = ???
  def getOptions(copyWidget: Boolean): TextMarkerOptions = ???
}

trait LineWidget extends WithEvents {
  def clear(): Unit = ???
  def changed(): Unit = ???
}

trait EditorChange extends js.Object {
  def from: Position = ???
  def to: Position = ???
  def text: js.Array[String] = ???
  def removed: String = ???
}

trait EditorChangeLinkedList extends EditorChange {
  def next: EditorChangeLinkedList = ???
}

trait EditorChangeCancellable extends EditorChange {
  def update(from: Position = ???, to: Position = ???, text: String = ???): Unit = ???
  def cancel(): Unit = ???
}

/**
 * Whenever points in the document are represented, the API uses objects with line and ch properties. Both are zero-based. CodeMirror makes sure to 'clip' any positions passed by client code so that they fit inside the document, so you shouldn't worry too much about sanitizing your coordinates. If you give ch a value of null, or don't specify it, it will be replaced with the length of the specified line.
 */
trait Position extends js.Object {
  /**
   * Zero based
   */
  var ch: Int = ???
  var line: Int = ???
}

object Position {
  def apply(ch: Int, line: Int): Position = {
    val result = js.Object().asInstanceOf[Position]
    result.ch = ch
    result.line = line
    return result
  }
}

trait PositionWithHitSide extends Position {
  var hitSide: js.UndefOr[Boolean] = ???
}

trait CodeMirrorCommands extends js.Object with Map[String, Function[CodeMirror, Unit]] {
  type Command = js.Function1[CodeMirror, Unit]
  /** Select the whole content of the editor. */
  var selectAll: Command = ???

  /** When multiple selections are present, this deselects all but the primary selection. */
  var singleSelection: Command = ???

  /** Emacs-style line killing. Deletes the part of the line after the cursor. If that consists only of whitespace, the newline at the end of the line is also deleted. */
  var killLine: Command = ???

  /** Deletes the whole line under the cursor, including newline at the end. */
  var deleteLine: Command = ???

  /** Delete the part of the line before the cursor. */
  var delLineLeft: Command = ???

  /** Delete the part of the line from the left side of the visual line the cursor is on to the cursor. */
  var delWrappedLineLeft: Command = ???

  /** Delete the part of the line from the cursor to the right side of the visual line the cursor is on. */
  var delWrappedLineRight: Command = ???

  /** Undo the last change. */
  var undo: Command = ???

  /** Redo the last undone change. */
  var redo: Command = ???

  /** Undo the last change to the selection, or if there are no selection-only changes at the top of the history, undo the last change. */
  var undoSelection: Command = ???

  /** Redo the last change to the selection, or the last text change if no selection changes remain. */
  var redoSelection: Command = ???

  /** Move the cursor to the start of the document. */
  var goDocStart: Command = ???

  /** Move the cursor to the end of the document. */
  var goDocEnd: Command = ???

  /** Move the cursor to the start of the line. */
  var goLineStart: Command = ???

  /** Move to the start of the text on the line, or if we are already there, to the actual start of the line (including whitespace). */
  var goLineStartSmart: Command = ???

  /** Move the cursor to the end of the line. */
  var goLineEnd: Command = ???

  /** Move the cursor to the right side of the visual line it is on. */
  var goLineRight: Command = ???

  /** Move the cursor to the left side of the visual line it is on. If this line is wrapped, that may not be the start of the line. */
  var goLineLeft: Command = ???

  /** Move the cursor to the left side of the visual line it is on. If that takes it to the start of the line, behave like goLineStartSmart. */
  var goLineLeftSmart: Command = ???

  /** Move the cursor up one line. */
  var goLineUp: Command = ???

  /** Move down one line. */
  var goLineDown: Command = ???

  /** Move the cursor up one screen, and scroll up by the same distance. */
  var goPageUp: Command = ???

  /** Move the cursor down one screen, and scroll down by the same distance. */
  var goPageDown: Command = ???

  /** Move the cursor one character left, going to the previous line when hitting the start of line. */
  var goCharLeft: Command = ???

  /** Move the cursor one character right, going to the next line when hitting the end of line. */
  var goCharRight: Command = ???

  /** Move the cursor one character left, but don't cross line boundaries. */
  var goColumnLeft: Command = ???

  /** Move the cursor one character right, don't cross line boundaries. */
  var goColumnRight: Command = ???

  /** Move the cursor to the start of the previous word. */
  var goWordLeft: Command = ???

  /** Move the cursor to the end of the next word. */
  var goWordRight: Command = ???

  /** Move to the left of the group before the cursor. A group is a stretch of word characters, a stretch of punctuation characters, a newline, or a stretch of more than one whitespace character. */
  var goGroupLeft: Command = ???

  /** Move to the right of the group after the cursor (see above). */
  var goGroupRight: Command = ???

  /** Delete the character before the cursor. */
  var delCharBefore: Command = ???

  /** Delete the character after the cursor. */
  var delCharAfter: Command = ???

  /** Delete up to the start of the word before the cursor. */
  var delWordBefore: Command = ???

  /** Delete up to the end of the word after the cursor. */
  var delWordAfter: Command = ???

  /** Delete to the left of the group before the cursor. */
  var delGroupBefore: Command = ???

  /** Delete to the start of the group after the cursor. */
  var delGroupAfter: Command = ???

  /** Auto-indent the current line or selection. */
  var indentAuto: Command = ???

  /** Indent the current line or selection by one indent unit. */
  var indentMore: Command = ???

  /** Dedent the current line or selection by one indent unit. */
  var indentLess: Command = ???

  /** Insert a tab character at the cursor. */
  var insertTab: Command = ???

  /** Insert the amount of spaces that match the width a tab at the cursor position would have. */
  var insertSoftTab: Command = ???

  /** If something is selected, indent it by one indent unit. If nothing is selected, insert a tab character. */
  var defaultTab: Command = ???

  /** Swap the characters before and after the cursor. */
  var transposeChars: Command = ???

  /** Insert a newline and auto-indent the new line. */
  var newlineAndIndent: Command = ???

  /** Flip the overwrite flag. */
  var toggleOverwrite: Command = ???

  /** Not defined by the core library, only referred to in key maps. Intended to provide an easy way for user code to define a save command. */
  var save: Command = ???

  /** Not defined by the core library, but defined in the search addon (or custom client addons). */
  var find: Command = ???

  /** Not defined by the core library, but defined in the search addon (or custom client addons). */
  var findNext: Command = ???

  /** Not defined by the core library, but defined in the search addon (or custom client addons). */
  var findPrev: Command = ???

  /** Not defined by the core library, but defined in the search addon (or custom client addons). */
  var replace: Command = ???

  /** Not defined by the core library, but defined in the search addon (or custom client addons). */
  var replaceAll: Command = ???

}

trait TextMarkerOptions extends js.Object {
  var className: String = ???
  var inclusiveLeft: Boolean = ???
  var inclusiveRight: Boolean = ???
  var atomic: Boolean = ???
  var collapsed: Boolean = ???
  var clearOnEnter: Boolean = ???
  var replacedWith: HTMLElement = ???
  var readOnly: Boolean = ???
  var addToHistory: Boolean = ???
  var startStyle: String = ???
  var endStyle: String = ???
  var shared: Boolean = ???
}