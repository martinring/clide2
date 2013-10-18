package clide.ghc

import clide.collaboration.Annotate
import clide.collaboration.Annotation
import clide.collaboration.Annotations
import clide.collaboration.Plain
import scala.util.parsing.combinator.RegexParsers

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
    println("parsing: " + s)
    LineParser.parse(LineParser.error,s).map(Some(_)).getOrElse(None)
  }
  
  trait GHCMessage
  case class Error extends GHCMessage
  case class Lint  extends GHCMessage  
    
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
          case "Error" => result = result.annotate(0, Map("e" -> e))
          case "Warning" => result = result.annotate(0, Map("w" -> e))
        }
        
    }                  
    result.plain(state.length - position)
  }
}