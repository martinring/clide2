package clide.client.codemirror.plugins

import clide.client.codemirror.CodeMirror
import scala.scalajs.js
import scala.scalajs.js.RegExp
import clide.client.codemirror.Position

object SearchCursor {
  implicit class SearchCursorExtension(cm: CodeMirror) extends js.Object {
    def getSearchCursor(query: String): Cursor[js.UndefOr[Boolean]] = js.native
    def getSearchCursor(query: String, start: Position): Cursor[js.UndefOr[Boolean]] = js.native
    def getSearchCursor(query: String, start: Position, caseFold: Boolean): Cursor[js.UndefOr[Boolean]] = js.native
    def getSearchCursor(query: RegExp): Cursor[js.UndefOr[js.Array[String]]] = js.native
    def getSearchCursor(query: RegExp, start: Position): Cursor[js.UndefOr[js.Array[String]]] = js.native
  }
  
  trait Cursor[R] extends js.Object {
    def findNext(): R = js.native
    def findPrevious(): R = js.native
    def from(): Position = js.native
    def to(): Position = js.native
    def replace(text: String): Unit = js.native
  }
}