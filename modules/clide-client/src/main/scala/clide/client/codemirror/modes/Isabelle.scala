package clide.client.codemirror.modes

import clide.client.interfaces._
import scala.scalajs.js.annotation.JSExport
import scala.scalajs.js.RegExp

case class IsabelleModeState(
  var verbatimLevel: Int = 0,
  var commentLevel: Int = 0,
  var command: String = null,
  var tokenize: (Stream,IsabelleModeState) => String)

object IsabelleMode {
  val greek       = RegExp("(?:\\\\<(?:alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|" +
      "mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|" +
      "Pi|Sigma|Upsilon|Phi|Psi|Omega)>)")
  val digit       = RegExp("[0-9]")
  val latin       = RegExp("[a-zA-Z]")
  val sym         = RegExp("[\\!\\#\\$\\%\\&\\*\\+\\-\\/\\<\\=\\>\\?\\@\\^\\_\\|\\~]")
  val letter      = RegExp(s"(?:${latin.source}|\\\\<${latin.source}{1,2}>|${greek.source}|\\\\<\\^isu[bp]>)")
  val quasiletter = RegExp(s"(?:${letter.source}|${digit.source}|\\_|\\')")
  val ident       = RegExp(s"(?:${letter.source}#{quasiletter*)")
  val longident   = RegExp(s"(?:${ident.source}(?:\\.${ident.source})+)")
  val symident    = RegExp(s"(?:${sym.source}+|\\\\<${ident.source}>)")
  val nat         = RegExp(s"(?:${digit.source}+)")
  val floating    = RegExp(s"(?:-?${nat.source}\\.${nat.source})")
  val variable    = RegExp(s"(?:\\?${ident.source}(?:\\.${nat.source})?)")
  val typefree    = RegExp(s"'${ident.source}")
  val typevar     = RegExp(s"\\?${typefree.source}(?:\\.${nat.source})")
  val num         = RegExp("#?-?[0-9]+(?:\\.[0-9]+)?")
  val escaped     = RegExp("\\[\"\\]")
  val speciale    = RegExp("\\<[A-Za-z]+>")
  val control     = RegExp("\\<\\^[A-Za-z]+>")
  val incomplete  = RegExp("\\<\\^{0,1}[A-Za-z]*>?")
  val lineComment = RegExp("--.*")  
}

@JSExport class IsabelleMode(config: EditorConfiguration, parserConfig: Any) extends Mode[IsabelleModeState] {
  println("making isabelle mode")
  
  def tokenBase(stream: Stream, state: IsabelleModeState): String = {
    println("tokenBase")
    val char = stream.peek().asInstanceOf[Char]
    
    if (char == '{') {
      stream.next()
      if (stream.eat("*") != null) {
        state.verbatimLevel += 1
        state.tokenize = tokenVerbatim
        return state.tokenize(stream,state)
      } else stream.backUp(1)
    }
     
    state.asInstanceOf[IsabelleModeState].command = null
    
    if (char == "\"") {
      stream.next()
      state.asInstanceOf[IsabelleModeState].tokenize = tokenString
      return "string"
    }
    
    if (char == "`") {
      stream.next()
      state.asInstanceOf[IsabelleModeState].tokenize = tokenAltString
      return "altstring"
    }
    
    if (char == "(") {
      stream.next()
      if (stream.eat("*") != null) {
        state.commentLevel += 1
        state.tokenize = tokenComment
        return state.tokenize(stream, state)
      } else stream.backUp(1)
    }
    
    if (stream.`match`(IsabelleMode.typefree) != null) "tfree"
    else if (stream.`match`(IsabelleMode.typevar) != null) "tvar"
    else if (stream.`match`(IsabelleMode.variable) != null) "var"
    else if (stream.`match`(IsabelleMode.longident) != null || stream.`match`(IsabelleMode.ident) != null) {
      "keyword"      
    }      
    else if (stream.`match`(IsabelleMode.symident) != null) "symbol"
    else if (stream.`match`(IsabelleMode.control) != null) "control"
    else if (stream.`match`(IsabelleMode.incomplete) != null) "incomplete" 
    else {
      stream.next()
      null
    }
  }
  
  def tokenVerbatim(stream: Stream, state: IsabelleModeState): String = {
    var prev: String = null
    var next: String = null
    while ({ next = stream.next(); next != null }) {
      if (prev == "*" && next == "}") {
        state.asInstanceOf[IsabelleModeState].tokenize = tokenBase
        "verbatim" + (if (state.command != null) " " + state.asInstanceOf[IsabelleModeState].command else "")
      }
    }
    "verbatim" + (if (state.command != null) " " + state.asInstanceOf[IsabelleModeState].command else "")
  }
  
  def tokenComment(stream: Stream, state: IsabelleModeState): String = {
    var prev: String = null
    var next: String = null
    stream.next()
    "comment"
  }  

  def tokenString(stream: Stream, state: IsabelleModeState): String = {
    val prev = null
    val next = null
    stream.next()
    "string"
  }

  def tokenAltString(stream: Stream, state: IsabelleModeState): String = {
    val prev = null
    val next = null
    stream.next()
    "alt-string"
  }

  
  def token(stream: Stream, state: IsabelleModeState): String = {
    stream.next()
    "keyword"
  }
  
  @JSExport def startState() = IsabelleModeState(0,0,null,token))
}

@JSExport
class C(p: String) extends T[String] {
  def method(x: Int) = p + x
}
