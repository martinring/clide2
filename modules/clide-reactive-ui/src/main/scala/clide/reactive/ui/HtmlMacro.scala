package clide.reactive.ui

import scala.reflect.macros.Context
import scala.language.experimental.macros
import org.scalajs.dom._
import scala.xml._
import org.xml.sax.SAXParseException

object HTMLMacro {
  implicit class HTMLCompiler(val sc: StringContext) extends AnyVal {
    def html(args: Any*): DocumentFragment = macro htmlCompiler
  }
  
  def htmlCompiler(c: Context)(args: c.Expr[Any]*): c.Expr[DocumentFragment] = {
    import c.universe._
    val parts = c.prefix.tree match {
      case Apply(_, List(Apply(_,parts))) =>
        parts.collect {
          case t @ Literal(Constant(const: String)) => (const, t.pos)
        }
      case _ =>
        c.abort(c.enclosingPosition, "Must be called in string interpolation")
    }
    val builder = new StringBuilder
    builder.append("<html>")
    if (parts.length > 0) {
      builder.append(parts.head._1)
      var pos = 0
      while (pos + 1 < parts.length) {
        builder.append("{{").append(pos.toString).append("}}")
        pos += 1
        builder.append(parts(pos)._1)
      }
    }
    builder.append("</html>")
    val xml = try {
      XML.loadString(builder.result)
    } catch {
      case e: SAXParseException => c.abort(c.enclosingPosition, e.getMessage())
    }
    xml.child.foreach {
      case Elem(prefix, label, attribs, scope, child @ _*) =>
        reify { document.createElement(label) }
      case Text(value) => 
        reify { document.createTextNode(value) }
    }
    reify { 
      val result = document.createDocumentFragment()
      result
    }
  }
}