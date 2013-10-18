package clide.ghc

import clide.collaboration.Annotate
import clide.collaboration.Annotation
import clide.collaboration.Annotations
import clide.collaboration.Plain
import scala.util.parsing.combinator.RegexParsers

object HaskellMarkup extends RegexParsers {
  def line: Parser[Int] = "[0-9]+".r ^^ { _.toInt }
  def ch:   Parser[Int] = "[0-9]+".r ^^ { _.toInt }
  def position: Parser[(Int,Int)] = ":" ~ line ~ ":" ~ ch ~ ":" ^^ {
    case _ ~ line ~ _ ~ ch ~ _ => (line,ch)
  }
  def output: Parser[String] = ".*".r
  def error: Parser[((Int,Int),String)] = position ~ output ^^ {
    case p ~ c => (p,c)
  }
  
  def toAnnotations(errors: List[((Int,Int),String)], state: String): Annotations = {
    var result = new Annotations
    val lines = state.split("\n").map(_.length() + 1).toList
    
    def offset(line: Int, ch: Int): Int = 
      lines.take(line-1).reduceOption(_ + _).getOrElse(0) + ch
    
    var position = 0
      
    errors.map({
      case ((l,c),e) => (offset(l,c),e)
    }).sortBy(_._1).foreach {
      case (o,e) => 
        if (o > position) {
          result = result.plain(o - position)
          position = o
        }                          
        result = result.annotate(0, Map("e" -> e))
    }                  
    result.plain(state.length - position)
  }
}