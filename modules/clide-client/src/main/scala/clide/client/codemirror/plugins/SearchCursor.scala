package clide.client.codemirror.plugins

import clide.client.codemirror.CodeMirror
import scala.scalajs.js
import scala.scalajs.js.RegExp
import clide.client.codemirror.Position

object SearchCursor {
  implicit class SearchCursorExtension(cm: CodeMirror) extends js.Object {
    def getSearchCursor(query: String): Cursor[js.UndefOr[Boolean]] = ???
    def getSearchCursor(query: String, start: Position): Cursor[js.UndefOr[Boolean]] = ???
    def getSearchCursor(query: String, start: Position, caseFold: Boolean): Cursor[js.UndefOr[Boolean]] = ???
    def getSearchCursor(query: RegExp): Cursor[js.UndefOr[js.Array[String]]] = ???
    def getSearchCursor(query: RegExp, start: Position): Cursor[js.UndefOr[js.Array[String]]] = ???
  }
  
  trait Cursor[R] extends js.Object {
    def findNext(): R = ???
    def findPrevious(): R = ???
    def from(): Position = ???
    def to(): Position = ???
    def replace(text: String): Unit = ???
  }
}