package clide.ghc

import clide.collaboration.Annotate
import clide.collaboration.Annotation
import clide.collaboration.Annotations
import clide.collaboration.Plain
import scala.util.parsing.combinator.RegexParsers
import clide.collaboration.AnnotationType

object HaskellMarkup {
  object LineParser extends RegexParsers {
    def line: Parser[Int] = "[0-9]+".r ^^ { _.toInt }
	def ch:   Parser[Int] = "[0-9]+".r ^^ { _.toInt }
	def t: Parser[String] = opt("Warning" <~ ":") ^^ { _.getOrElse("Error") }
	def position: Parser[(Int,Int)] = line ~ ":" ~ ch ~ ":" ^^ {
	  case line ~ _ ~ ch ~ _ => (line,ch)
	}
	def output: Parser[String] = ".*".r ^^ { _.split("    +").mkString("\n")}
	def error: Parser[((Int,Int),String,String)] = position ~ t ~ output ^^ {
	  case p ~ t ~ c => (p,t,c)
	}	 
  }
  
  def parseLine(s: String) = {
    LineParser.parse(LineParser.error,s).map(Some(_)).getOrElse(None)
  }
  
  trait GHCMessage
  case class Error extends GHCMessage
  case class Lint  extends GHCMessage  
    
  def substitutions(state: String, as: Annotations = new Annotations): Annotations = state match {
    case "" => as
    case _  =>
      val i = state.indexOf("->")
      if (i >= 0) substitutions(state.drop(i + 2), as.plain(i).annotate(2, Set(AnnotationType.Class -> "symbol", AnnotationType.Substitution ->"→")))      
      else as.plain(state.length)        
  }
  
  def toAnnotations(errors: List[((Int,Int),String,String)], state: String): Annotations = {
    var result = new Annotations
    val lines = state.split("\n").map(_.length() + 1).toList
    
    def offset(line: Int, ch: Int): Int = 
      lines.take(line-1).reduceOption(_ + _).getOrElse(0) + ch
    
    var position = 0
      
    errors.map({
      case ((l,c),t,e) => (offset(l,c),t,e)
    }).sortBy(_._1).foreach {
      case (o,t,e) =>
        if (o > position) {
          result = result.plain(o - position)
          position = o
        }
        t match {
          case "Error" => result = result.annotate(0, Set(AnnotationType.ErrorMessage -> e))
          case "Warning" => result = result.annotate(0, Set(AnnotationType.WarningMessage -> e))
        }
        
    }                  
    result.plain(state.length - position)
  }
}