package clide.client.interfaces

import org.scalajs.dom.{Event, HTMLElement, HTMLTextAreaElement}

import scala.scalajs.js
import scala.scalajs.js._
import scala.scalajs.js.annotation.JSName

trait WithEvents extends js.Object {
  def on(eventName: String, handler: js.Function1[Editor, Unit]): Unit = ???
  def off(eventName: String, handler: js.Function1[Editor, Unit]): Unit = ???  
}

trait Editor extends WithEvents {
  def hasFocus(): Boolean = ???
  def findPosH(start: Position, amount: Int, unit: String, visually: Boolean): js.Any = ???
  def findPosV(start: Position, amount: Int, unit: String): js.Any = ???
  def findWordAt(pos: Position): Range = ???
  def setOption(option: String, value: js.Any): Unit = ???
  def getOption(option: String): js.Dynamic = ???
  def addKeyMap(map: js.Any, bottom: Boolean = ???): Unit = ???
  def removeKeyMap(map: js.Any): Unit = ???
  def addOverlay(mode: js.Any, options: js.Any = ???): Unit = ???
  def removeOverlay(mode: js.Any): Unit = ???
  def getDoc(): Doc = ???
  def swapDoc(doc: Doc): Doc = ???
  def setGutterMarker(line: js.Any, gutterID: String, value: HTMLElement): LineHandle = ???
  def clearGutter(gutterID: String): Unit = ???
  def addLineClass(line: js.Any, where: String, _clazz: String): LineHandle = ???
  def removeLineClass(line: js.Any, where: String, clazz: String): LineHandle = ???
  def lineInfo(line: js.Any): js.Any = ???
  def addWidget(pos: Position, node: HTMLElement, scrollIntoView: Boolean): Unit = ???
  def addLineWidget(line: js.Any, node: HTMLElement, options: js.Any = ???): LineWidget = ???
  def setSize(width: js.Any, height: js.Any): Unit = ???
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

@JSName("Doc")
class Doc protected () extends WithEvents {
  def this(text: String, mode: js.Any = ???, firstLineNumber: Int = ???) = this()
  def getValue(seperator: String = ???): String = ???
  def setValue(content: String): Unit = ???
  def getRange(from: Position, to: Position, seperator: String = ???): String = ???
  def replaceRange(replacement: String, from: Position, to: Position): Unit = ???
  def getLine(n: Int): String = ???
  def setLine(n: Int, text: String): Unit = ???
  def removeLine(n: Int): Unit = ???
  def lineCount(): Int = ???
  def firstLine(): Int = ???
  def lastLine(): Int = ???
  def getLineHandle(num: Int): LineHandle = ???
  def getLineNumber(handle: LineHandle): Int = ???
  def eachLine(f: js.Function1[LineHandle, Unit]): Unit = ???
  def eachLine(start: Int, end: Int, f: js.Function1[LineHandle, Unit]): Unit = ???
  def markClean(): Unit = ???
  def isClean(): Boolean = ???
  def getSelection(): String = ???
  def replaceSelection(replacement: String, collapse: String = ???): Unit = ???
  def getCursor(start: String = ???): Position = ???
  def somethingSelected(): Boolean = ???
  def setCursor(pos: Position): Unit = ???
  def setSelection(anchor: Position, head: Position): Unit = ???
  def extendSelection(from: Position, to: Position = ???): Unit = ???
  def setExtending(value: Boolean): Unit = ???
  def getEditor(): Editor = ???
  def copy(copyHistory: Boolean): Doc = ???
  def linkedDoc(options: js.Any): Doc = ???
  def unlinkDoc(doc: Doc): Unit = ???
  def iterLinkedDocs(fn: js.Function2[Doc, Boolean, Unit]): Unit = ???
  def undo(): Unit = ???
  def redo(): Unit = ???
  def historySize(): js.Any = ???
  def clearHistory(): Unit = ???
  def getHistory(): js.Dynamic = ???
  def setHistory(history: js.Any): Unit = ???
  def markText(from: Position, to: Position, options: TextMarkerOptions = ???): TextMarker = ???
  def setBookmark(pos: Position, options: js.Any = ???): TextMarker = ???
  def findMarksAt(pos: Position): js.Array[TextMarker] = ???
  def getAllMarks(): js.Array[TextMarker] = ???
  def getMode(): js.Dynamic = ???
  def posFromIndex(index: Int): Position = ???
  def indexFromPos(`object`: Position): Int = ???  
}

trait Range extends js.Object {
  def anchor: Position = ???
  def head: Position = ???
}

trait LineHandle extends WithEvents {
  var text: String = ???
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

trait Position extends js.Object {
  var ch: Int = ???
  var line: Int = ???
}

class EditorConfiguration extends js.Object {
  var value: js.Any = ???
  var mode: js.Any = ???
  var theme: String = ???
  var indentUnit: Int = ???
  var smartIndent: Boolean = ???
  var tabSize: Int = ???
  var indentWithTabs: Boolean = ???
  var electricChars: Boolean = ???
  var rtlMoveVisually: Boolean = ???
  var keyMap: String = ???
  var extraKeys: js.Any = ???
  var lineWrapping: Boolean = ???
  var lineNumbers: Boolean = ???
  var firstLineNumber: Int = ???
  var lineNumberFormatter: js.Function1[Int, String] = ???
  var gutters: js.Array[String] = ???
  var fixedGutter: Boolean = ???
  var readOnly: js.Any = ???
  var showCursorWhenSelecting: Boolean = ???
  var undoDepth: Int = ???
  var historyEventDelay: Int = ???
  var tabindex: Int = ???
  var autofocus: Boolean = ???
  var dragDrop: Boolean = ???
  var onDragEvent: js.Function2[Editor, Event, Boolean] = ???
  var onKeyEvent: js.Function2[Editor, Event, Boolean] = ???
  var cursorBlinkRate: Int = ???
  var cursorHeight: Int = ???
  var workTime: Int = ???
  var workDelay: Int = ???
  var pollInterval: Int = ???
  var flattenSpans: Boolean = ???
  var maxHighlightLength: Int = ???
  var viewportMargin: Int = ???
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

@JSName("CodeMirror")
object CodeMirror extends js.Object {
  def Pass: js.Any = ???
  def fromTextArea(host: HTMLTextAreaElement, options: EditorConfiguration = ???): Editor = ???
  def version: String = ???
  def defineExtension(name: String, value: js.Any): Unit = ???
  def defineDocExtension(name: String, value: js.Any): Unit = ???
  def defineOption(name: String, default: js.Any, updateFunc: js.Function): Unit = ???
  def defineInitHook(func: js.Function): Unit = ???
  def on(element: js.Any, eventName: String, handler: js.Function): Unit = ???
  def off(element: js.Any, eventName: String, handler: js.Function): Unit = ???
}

