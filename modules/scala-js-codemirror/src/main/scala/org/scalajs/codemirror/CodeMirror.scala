package org.scalajs

import scala.scalajs.js
import scala.scalajs.js.annotation._
import org.scalajs.dom._

class CodeMirror private () extends js.Object {  
  def this(host: HTMLElement) = this()
  def this(host: HTMLElement, options: EditorConfiguration) = this()
  def this(callback: js.Function1[HTMLElement, Unit], options: EditorConfiguration) = this()
  def this(callback: js.Function1[HTMLElement, Unit]) = this()
  
  def hasFocus(): js.Boolean = ???
  def findPosH(start: Pos, amount: js.Number, unit: js.String, visually: js.Boolean): js.Any = ???
  def findPosV(start: Pos, amount: js.Number, unit: js.String): js.Any = ???
  def setOption(option: js.String, value: js.Any): js.Dynamic = ???
  def getOption(option: js.String): js.Dynamic = ???
  def addKeyMap(map: js.Any, bottom: js.Boolean): js.Dynamic = ???
  def addKeyMap(map: js.Any): js.Dynamic = ???
  def removeKeyMap(map: js.Any): js.Dynamic = ???
  def addOverlay(mode: js.Any, options: js.Any): js.Dynamic = ???
  def addOverlay(mode: js.Any): js.Dynamic = ???
  def removeOverlay(mode: js.Any): js.Dynamic = ???
  def getDoc(): Doc = ???
  def swapDoc(doc: Doc): Doc = ???
  def setGutterMarker(line: js.Any, gutterID: js.String, value: HTMLElement): LineHandle = ???
  def clearGutter(gutterID: js.String): js.Dynamic = ???
  def addLineClass(line: js.Any, where: js.String, _class_ : js.String): LineHandle = ???
  def removeLineClass(line: js.Any, where: js.String, class_ : js.String): LineHandle = ???
  def lineInfo(line: js.Any): js.Any = ???
  def addWidget(pos: Pos, node: HTMLElement, scrollIntoView: js.Boolean): js.Dynamic = ???
  def addLineWidget(line: js.Any, node: HTMLElement, options: js.Any): LineWidget = ???
  def addLineWidget(line: js.Any, node: HTMLElement): LineWidget = ???
  def setSize(width: js.Any, height: js.Any): js.Dynamic = ???
  def scrollTo(x: js.Number, y: js.Number): js.Dynamic = ???
  def getScrollInfo(): js.Any = ???
  def scrollIntoView(pos: Pos, margin: js.Number): js.Dynamic = ???
  def scrollIntoView(pos: Pos): js.Dynamic = ???
  def scrollIntoView(pos: js.Any, margin: js.Number): js.Dynamic = ???
  def cursorCoords(where: js.Boolean, mode: js.String): js.Any = ???
  def cursorCoords(where: Pos, mode: js.String): js.Any = ???
  def charCoords(pos: Pos, mode: js.String): js.Any = ???
  def coordsChar(`object`: js.Any, mode: js.String): Pos = ???
  def coordsChar(`object`: js.Any): Pos = ???
  def defaultTextHeight(): js.Number = ???
  def defaultCharWidth(): js.Number = ???
  def getViewport(): js.Any = ???
  def refresh(): js.Dynamic = ???
  def getTokenAt(pos: Pos): js.Any = ???
  def getStateAfter(line: js.Number): js.Dynamic = ???
  def getStateAfter(): js.Dynamic = ???
  def operation[T](fn: js.Function0[T]): T = ???
  def indentLine(line: js.Number, dir: js.String): js.Dynamic = ???
  def indentLine(line: js.Number): js.Dynamic = ???
  def focus(): js.Dynamic = ???
  def getInputField(): HTMLTextAreaElement = ???
  def getWrapperElement(): HTMLElement = ???
  def getScrollerElement(): HTMLElement = ???
  def getGutterElement(): HTMLElement = ???
  def on(eventName: js.String, handler: js.Function1[CodeMirror, Unit]): js.Dynamic = ???
  def off(eventName: js.String, handler: js.Function1[CodeMirror, Unit]): js.Dynamic = ???
}

@JSName("CodeMirror.Doc")
class Doc extends js.Object {  
  def this(text: js.String, mode: js.Any, firstLineNumber: js.Number) = this()
  def this(text: js.String, mode: js.Any) = this()
  def this(text: js.String) = this()
  def getValue(seperator: js.String): js.String = ???
  def getValue(): js.String = ???
  def setValue(content: js.String): js.Dynamic = ???
  def getRange(from: Pos, to: Pos, seperator: js.String): js.String = ???
  def getRange(from: Pos, to: Pos): js.String = ???
  def replaceRange(replacement: js.String, from: Pos, to: Pos): js.Dynamic = ???
  def getLine(n: js.Number): js.String = ???
  def setLine(n: js.Number, text: js.String): js.Dynamic = ???
  def removeLine(n: js.Number): js.Dynamic = ???
  def lineCount(): js.Number = ???
  def firstLine(): js.Number = ???
  def lastLine(): js.Number = ???
  def getLineHandle(num: js.Number): LineHandle = ???
  def getLineNumber(handle: LineHandle): js.Number = ???
  def eachLine(f: js.Function1[LineHandle, Unit]): js.Dynamic = ???
  def eachLine(start: js.Number, end: js.Number, f: js.Function1[LineHandle, Unit]): js.Dynamic = ???
  def markClean(): js.Dynamic = ???
  def isClean(): js.Boolean = ???
  def getSelection(): js.String = ???
  def replaceSelection(replacement: js.String, collapse: js.String): js.Dynamic = ???
  def replaceSelection(replacement: js.String): js.Dynamic = ???
  def getCursor(start: js.String): Pos = ???
  def getCursor(): Pos = ???
  def somethingSelected(): js.Boolean = ???
  def setCursor(pos: Pos): js.Dynamic = ???
  def setSelection(anchor: Pos, head: Pos): js.Dynamic = ???
  def extendSelection(from: Pos, to: Pos): js.Dynamic = ???
  def extendSelection(from: Pos): js.Dynamic = ???
  def setExtending(value: js.Boolean): js.Dynamic = ???
  def getEditor(): CodeMirror = ???
  def copy(copyHistory: js.Boolean): Doc = ???
  def linkedDoc(options: js.Any): Doc = ???
  def unlinkDoc(doc: Doc): js.Dynamic = ???
  def iterLinkedDocs(fn: js.Function2[Doc, js.Boolean, Unit]): js.Dynamic = ???
  def undo(): js.Dynamic = ???
  def redo(): js.Dynamic = ???
  def historySize(): js.Any = ???
  def clearHistory(): js.Dynamic = ???
  def getHistory(): js.Dynamic = ???
  def setHistory(history: js.Any): js.Dynamic = ???
  def markText(from: Pos, to: Pos, options: TextMarkerOptions): TextMarker = ???
  def markText(from: Pos, to: Pos): TextMarker = ???
  def setBookmark(pos: Pos, options: js.Any): TextMarker = ???
  def setBookmark(pos: Pos): TextMarker = ???
  def findMarksAt(pos: Pos): js.Array[TextMarker] = ???
  def getAllMarks(): js.Array[TextMarker] = ???
  def getMode(): js.Dynamic = ???
  def posFromIndex(index: js.Number): Pos = ???
  def indexFromPos(`object`: Pos): js.Number = ???
}

@JSName("LineHandle")
trait LineHandle extends js.Object {
  var text: js.String = _
}

@JSName("TextMarker")
trait TextMarker extends js.Object {
  def clear(): js.Dynamic = ???
  def find(): Pos = ???
  def getOptions(copyWidget: js.Boolean): TextMarkerOptions = ???
}

@JSName("LineWidget")
trait LineWidget extends js.Object {
  def clear(): Unit = ???
  def changed(): js.Dynamic = ???
}

@JSName("EditorChange")
trait EditorChange extends js.Object {
  var from: Pos = _
  var to: Pos = _
  var text: js.Array[js.String] = _
  var removed: js.String = _
}

@JSName("EditorChangeLinkedList")
trait EditorChangeLinkedList extends EditorChange {
  var next: EditorChangeLinkedList = _
}

@JSName("EditorChangeCancellable")
trait EditorChangeCancellable extends EditorChange {
  def update(from: Pos, to: Pos, text: js.String): js.Dynamic = ???
  def update(from: Pos, to: Pos): js.Dynamic = ???
  def update(from: Pos): js.Dynamic = ???
  def update(): js.Dynamic = ???
  def cancel(): js.Dynamic = ???
}

@JSName("Pos")
trait Pos extends js.Object {
  var ch: js.Number = _
  var line: js.Number = _
}

@JSName("EditorConfiguration")
trait EditorConfiguration extends js.Object {
  var value: js.Any = _
  var mode: js.Any = _
  var theme: js.String = _
  var indentUnit: js.Number = _
  var smartIndent: js.Boolean = _
  var tabSize: js.Number = _
  var indentWithTabs: js.Boolean = _
  var electricChars: js.Boolean = _
  var rtlMoveVisually: js.Boolean = _
  var keyMap: js.String = _
  var extraKeys: js.Any = _
  var lineWrapping: js.Boolean = _
  var lineNumbers: js.Boolean = _
  var firstLineNumber: js.Number = _
  var lineNumberFormatter: js.Function1[js.Number, js.String] = _
  var gutters: js.Array[js.String] = _
  var fixedGutter: js.Boolean = _
  var readOnly: js.Any = _
  var showCursorWhenSelecting: js.Boolean = _
  var undoDepth: js.Number = _
  var historyEventDelay: js.Number = _
  var tabindex: js.Number = _
  var autofocus: js.Boolean = _
  var dragDrop: js.Boolean = _
  var onDragEvent: js.Function2[CodeMirror, Event, js.Boolean] = _
  var onKeyEvent: js.Function2[CodeMirror, Event, js.Boolean] = _
  var cursorBlinkRate: js.Number = _
  var cursorHeight: js.Number = _
  var workTime: js.Number = _
  var workDelay: js.Number = _
  var pollInterval: js.Number = _
  var flattenSpans: js.Boolean = _
  var maxHighlightLength: js.Number = _
  var viewportMargin: js.Number = _
}

@JSName("TextMarkerOptions")
trait TextMarkerOptions extends js.Object {
  var className: js.String = _
  var inclusiveLeft: js.Boolean = _
  var inclusiveRight: js.Boolean = _
  var atomic: js.Boolean = _
  var collapsed: js.Boolean = _
  var clearOnEnter: js.Boolean = _
  var replacedWith: HTMLElement = _
  var readOnly: js.Boolean = _
  var addToHistory: js.Boolean = _
  var startStyle: js.String = _
  var endStyle: js.String = _
  var shared: js.Boolean = _
}

object CodeMirror extends js.Object {
  def fromTextArea(host: HTMLTextAreaElement, options: EditorConfiguration): CodeMirror = ???
  def fromTextArea(host: HTMLTextAreaElement): CodeMirror = ???
  val version: js.String = ???
  def defineExtension(name: js.String, value: js.Any): js.Dynamic = ???
  def defineDocExtension(name: js.String, value: js.Any): js.Dynamic = ???
  def defineOption(name: js.String, default: js.Any, updateFunc: js.Function): js.Dynamic = ???
  def defineInitHook(func: js.Function): js.Dynamic = ???
  def on(element: js.Any, eventName: js.String, handler: js.Function): js.Dynamic = ???
  def off(element: js.Any, eventName: js.String, handler: js.Function): js.Dynamic = ???
}