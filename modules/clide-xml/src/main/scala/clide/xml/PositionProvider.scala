package clide.xml

import scala.reflect.macros.Context
import scala.reflect.io.AbstractFile
import scala.io.Source
import scala.reflect.internal.util.BatchSourceFile
import scala.reflect.internal.util.OffsetPosition

trait PositionProvider[T <: Context] {
  val context: T
  def offset(n: Int): context.Position
}

object PositionProvider {
  def forFile(c: Context)(path: String) = {    
    val af = AbstractFile.getFile(path)
    val content = Source.fromFile(path).mkString
    val sf = new BatchSourceFile(af, content)
    
    new PositionProvider[c.type] {
      val context: c.type = c
    
      def offset(n: Int): context.universe.Position = {
        new OffsetPosition(sf, n).asInstanceOf[context.universe.Position]
      }
      
      def lineColumn(line: Int, column: Int): context.universe.Position = {
        new OffsetPosition(sf, content.split("\n").map(_.length).take(line).sum + column).asInstanceOf[context.universe.Position]
      }
    }
  }
  
  def forLiteral(c: Context)(literal: c.universe.Tree) = {
    c.info(literal.pos, literal.pos.start + " to " + literal.pos.end, true)
    
    new PositionProvider[c.type] {
      val context: c.type = c
      
      def offset(n: Int): context.universe.Position = {
        literal.pos
      }
    }
  }
}