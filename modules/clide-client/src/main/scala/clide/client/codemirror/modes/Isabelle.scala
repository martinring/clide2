package clide.client.codemirror.modes

import clide.client.codemirror._
import scala.scalajs.js.annotation.JSExport
import scala.scalajs.js.RegExp
import scala.scalajs.js

case class IsabelleModeState(
  var commentLevel: Int = 0,
  var command: String = null,
  var tokenize: (Stream,IsabelleModeState) => String)

trait IsabelleModeConfig extends js.Object {
  def words: js.Dictionary[String]
}
  
object IsabelleMode {
  val Rgreek       = "(?:\\\\<(?:alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|" +
      "mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|" +
      "Pi|Sigma|Upsilon|Phi|Psi|Omega)>)"
  val Rdigit       = "[0-9]"
  val Rlatin       = "[a-zA-Z]"
  val Rsym         = "[\\!\\#\\$\\%\\&\\*\\+\\-\\/\\<\\=\\>\\?\\@\\^\\_\\|\\~]"
  val Rletter      = RegExp(s"(?:$Rlatin|\\\\<$Rlatin{1,2}>|$Rgreek|\\\\<\\^isu[bp]>)")
  val quasiletter = RegExp(s"(?:$Rletter|$Rdigit|\\_|\\')")
  val Rident      = s"(?:$Rletter$quasiletter*)"
  val ident       = RegExp(Rident)
  val longident   = RegExp(s"(?:$Rident(?:\\.$Rident)+)")
  val symident    = RegExp(s"(?:$Rsym+|\\\\<$Rident>)")
  val Rnat        = s"(?:$Rdigit+)"
  val nat         = RegExp(Rnat)
  val floating    = RegExp(s"(?:-?$Rnat}\\.$Rnat)")
  val variable    = RegExp(s"(?:\\?$Rident}(?:\\.$Rnat)?)")
  val Rtypefree   = s"'$Rident"
  val typefree    = RegExp(Rtypefree)
  val typevar     = RegExp(s"\\?$Rtypefree(?:\\.$Rnat)")
  val num         = RegExp("#?-?[0-9]+(?:\\.[0-9]+)?")
  val escaped     = RegExp("\\[\"\\]")
  val speciale    = RegExp("\\<[A-Za-z]+>")
  val control     = RegExp("\\<\\^[A-Za-z]+>")
  val incomplete  = RegExp("\\<\\^{0,1}[A-Za-z]*>?")
  val lineComment = RegExp("--.*")
}

@JSExport class IsabelleMode(config: CodeMirrorConfiguration, parserConfig: IsabelleModeConfig) extends Mode[IsabelleModeState] {
  println("making isabelle mode")
  
  def tokenBase(stream: Stream, state: IsabelleModeState): String = {    
    val char = stream.peek()    
    
    if (char == "{") {
      stream.next()
      if (stream.eat("*") != null) {
        state.tokenize = tokenVerbatim
        return state.tokenize(stream,state)
      } else stream.backUp(1)
    }
     
    state.command = null
    
    if (char == "\"") {
      stream.next()
      state.tokenize = tokenString
      return state.tokenize(stream, state)
    }
    
    if (char == "`") {
      stream.next()
      state.tokenize = tokenAltString
      return state.tokenize(stream, state)
    }
    
    if (char == "(") {
      if (stream.`match`("(*") exists identity) {
        state.commentLevel += 1
        state.tokenize = tokenComment
        return state.tokenize(stream, state)
      } else stream.backUp(1)
    }
    
    if (stream.`match`(IsabelleMode.typefree) != null) "tfree"
    else if (stream.`match`(IsabelleMode.typevar)  != null) "tvar"
    else if (stream.`match`(IsabelleMode.variable)  != null) "var"
    else if (stream.`match`(IsabelleMode.longident) != null || stream.`match`(IsabelleMode.ident) != null) {
      println(stream.current())
      parserConfig.words.getOrElse(stream.current(),"identifier") match {
        case "command" => 
          state.command = stream.current()
          s"command ${state.command}"
        case t => t        
      }
      
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
    if (stream.skipTo('*') exists identity) {
      stream.next()
      if (stream.eat("}").isDefined) {
        state.tokenize = tokenBase
        "verbatim" + (if (state.command != null) " " + state.command else "")
      } else state.tokenize(stream,state)
    }
    else {
      stream.skipToEnd()
      "verbatim"
    }
  }
  
  def tokenComment(stream: Stream, state: IsabelleModeState): String = {
    if (stream.skipTo('*') exists identity) {
      stream.next()
      if (stream.eat(")").isDefined) {
        state.tokenize = tokenBase
        "comment"
      } else state.tokenize(stream,state)
    }
    else {
      stream.skipToEnd()
      "comment"
    }
  }  

  def tokenString(stream: Stream, state: IsabelleModeState): String = {
    if (stream.skipTo('"') exists identity) {
      stream.next()
      state.tokenize = tokenBase
      "string"
    }
    else {
      stream.skipToEnd()
      "string"
    }    
  }

  def tokenAltString(stream: Stream, state: IsabelleModeState): String = {
    if (stream.skipTo('`') exists identity) {
      stream.next()
      state.tokenize = tokenBase
      "alt-string"
    }
    else {
      stream.skipToEnd()
      "alt-string"
    }    
  }

  
  def token(stream: Stream, state: IsabelleModeState): String = {
    state.tokenize(stream,state)
  }
  
  override def startState() = IsabelleModeState(0,null,tokenBase)
}