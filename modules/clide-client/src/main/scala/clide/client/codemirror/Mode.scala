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


trait Stream {
  def eol(): Boolean = ???
  def sol(): Boolean = ???
  def peek(): js.String = ???
  def next(): js.String = ???
  def eat(`match`: String): js.String = ???
  def eat(`match`: RegExp): js.String = ???
  def eat(`match`: js.Function1[js.String, Boolean]): js.String = ???
  def eatWhile(`match`: String): Boolean = ???
  def eatWhile(`match`: RegExp): Boolean = ???
  def eatWhile(`match`: js.Function1[js.String, Boolean]): Boolean = ???
  def skipToEnd(): Unit = ???
  def skipTo(char: js.String) = ???
  def `match`(pattern: String, consume: Boolean, caseFold: Boolean): Boolean = ???
  def `match`(pattern: String, consume: Boolean): Boolean = ???
  def `match`(pattern: String): Boolean = ???
  def `match`(pattern: RegExp, consume: Boolean): js.Array[String] = ???
  def `match`(pattern: RegExp): js.Array[String] = ???
  def backUp(n: Integer): Unit = ???
  def column(): Int = ???
  def indentation(): Int = ???
  def current(): String = ???
}