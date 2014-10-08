package clide.client.codemirror

import scala.scalajs.js.annotation.JSExport
import scala.scalajs.js
import scala.scalajs.js.RegExp

trait Mode[S] {
  @JSExport def startState(): S = js.undefined.asInstanceOf[S]
  @JSExport def token(stream: Stream, state: S): String
} 

trait BlankLineBehavior[S] { self: Mode[S] =>
  @JSExport def blankLine(state: S): S  
}

trait CopyStateBehavior[S] { self: Mode[S] =>
  @JSExport def copyState(state: S): S
}

trait CommentingBehavior { self: Mode[_] =>
  @JSExport def lineComment(): String = js.undefined.asInstanceOf[String]
  @JSExport def blockCommentStart(): String = js.undefined.asInstanceOf[String]
  @JSExport def blockCommentEnd(): String = js.undefined.asInstanceOf[String]
  @JSExport def blockCommentLead: String = js.undefined.asInstanceOf[String]
}

trait ElectricCharBehavior { slef: Mode[_] =>
  @JSExport def electricChars: String = js.undefined.asInstanceOf[String]
  @JSExport def electricInput: String = js.undefined.asInstanceOf[String]
}

trait Stream extends js.Object {
  def eol(): js.UndefOr[Boolean] = ???
  def sol(): js.UndefOr[Boolean] = ???
  def peek(): String = ???
  def next(): String = ???
  def eat(`match`: String): js.UndefOr[String] = ???
  def eat(`match`: RegExp): js.UndefOr[String] = ???
  def eat(`match`: js.Function1[js.String, Boolean]): js.UndefOr[String] = ???
  def eatSpace(): js.UndefOr[Boolean] = ???
  def eatWhile(`match`: String): js.UndefOr[Boolean] = ???
  def eatWhile(`match`: RegExp): js.UndefOr[Boolean] = ???
  def eatWhile(`match`: js.Function1[js.String, Boolean]): js.UndefOr[Boolean] = ???  
  def skipToEnd(): Unit = ???
  def skipTo(char: Char): js.UndefOr[Boolean] = ???
  def `match`(pattern: String, consume: Boolean, caseFold: Boolean): js.UndefOr[Boolean] = ???
  def `match`(pattern: String, consume: Boolean): js.UndefOr[Boolean] = ???
  def `match`(pattern: String): js.UndefOr[Boolean] = ???
  def `match`(pattern: RegExp, consume: Boolean): js.Array[String] = ???
  def `match`(pattern: RegExp): js.Array[String] = ???
  def backUp(n: Integer): Unit = ???
  def column(): Int = ???
  def indentation(): Int = ???
  def current(): String = ???    
}

object Stream {
  implicit class StreamOps(stream: Stream) extends Iterable[Char] {
    def nextOption = Option(stream.next()).map(_.asInstanceOf[Char])
    
    def iterator = new Iterator[Char] {
      private var _next: String = null
      
      def hasNext = _next != null || {        
        _next = stream.next()
        _next != null
      }
      
      def next() = if (_next != null) {
        val result = _next.asInstanceOf[Char]
        _next = null
        result
      } else {
        stream.next().asInstanceOf[Char]
      }
    }
  }
}