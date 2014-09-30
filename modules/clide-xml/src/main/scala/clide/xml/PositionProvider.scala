package clide.xml

import scala.reflect.macros.whitebox.Context
import scala.reflect.io.AbstractFile
import scala.io.Source
import scala.reflect.internal.util.BatchSourceFile
import scala.reflect.internal.util.OffsetPosition
import scala.reflect.internal.util.RangePosition

private [xml] trait PositionProvider[T <: Context] {
  val context: T
  def offset(n: Int): context.universe.Position
  def lineColumn(line: Int, column: Int): context.universe.Position
}

private [xml] object PositionProvider {
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
        new OffsetPosition(sf, sf.lineToOffset(line) + column).asInstanceOf[context.universe.Position]
      }
    }
  }
  
  def forLiteral(c: Context)(literal: c.universe.Tree) = {
    c.info(literal.pos, literal.pos.start + " to " + literal.pos.end, true)
    
    new PositionProvider[c.type] {
      val context: c.type = c
      
      def offset(n: Int): context.universe.Position = {        
        new OffsetPosition(literal.pos.source, literal.pos.start + n).asInstanceOf[context.universe.Position]
      }
      
      def lineColumn(line: Int, column: Int): context.universe.Position = {
        val offset = literal.pos.start 
          + literal.pos.source.lineToOffset(literal.pos.line + line) 
          + (if (line == 0) literal.pos.column + column else column)
        new OffsetPosition(literal.pos.source, offset).asInstanceOf[context.universe.Position]
      }
    }
  }
}