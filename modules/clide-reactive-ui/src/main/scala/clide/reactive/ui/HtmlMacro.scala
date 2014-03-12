package clide.reactive.ui

import scala.reflect.macros.Context
import scala.language.experimental.macros
import org.scalajs.dom._
import scala.xml._
import org.xml.sax.SAXParseException
import scala.reflect.api.Universe
import scala.collection.mutable.Buffer

trait Template[T <: InsertedView] {
  def render(context: InsertionContext): T
}

object HTMLMacro {
  implicit class HTMLCompiler(val sc: StringContext) extends AnyVal {
    def html(args: Any*): Any = macro htmlCompiler
  }
  
  def htmlCompiler(c: Context)(args: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    import Flag._
    // read raw string parts
    val parts = c.prefix.tree match {
      case Apply(_, List(Apply(_,parts))) =>
        parts.collect {
          case t @ Literal(Constant(const: String)) => (const, t.pos)
        }
      case _ =>
        c.abort(c.enclosingPosition, "htmlCompiler may only be called through plain string interpolation")
    }
    // Build html string
    val builder = new StringBuilder
    builder.append("<html>")
    if (parts.nonEmpty) {
      builder.append(parts.head._1)
      var pos = 0
      while (pos + 1 < parts.length) {
        builder.append("{{").append(pos.toString).append("}}")
        pos += 1
        builder.append(parts(pos)._1)
      }
    }
    builder.append("</html>")
    // Parse xml
    val xml = try {
      XML.loadString(builder.result)
    } catch {
      // Abort with parse errors
      case e: SAXParseException => c.abort(c.enclosingPosition, e.getMessage())
    }    
    // Build reified dom construction code
    var elemCounter = 0
    def nextName() = {
      elemCounter += 1
      newTermName("$elem_" + elemCounter)
    }
    val accessorInterfaces = Buffer.empty[Tree]
    val accessorImpls = Buffer.empty[Tree]
    def createChildren(parent: TermName, xml: Seq[scala.xml.Node]): Iterable[Tree] = xml.flatMap {
      case Elem(prefix, label, attribs, scope, child @ _*) =>
        val elemName = nextName()
        accessorInterfaces ++= createGetterInterfaces(attribs)
        accessorInterfaces ++= createSetterInterfaces(attribs)
        accessorImpls ++= createGetterImpls(elemName, attribs)
        accessorImpls ++= createSetterImpls(elemName, attribs)
        List(q"""val $elemName = dom.document.createElement($label)""") ++ applyAttributes(elemName,attribs) ++
        List(q"""$parent.appendChild($elemName)""") ++ createChildren(elemName,child)
      case Text(value) =>
        val buf = Buffer.empty[Tree]
        val elemName = nextName()
        val regex = "\\{\\{([0-9]+)\\}\\}".r
        var remaining = value.trim()
        var current = regex.findFirstMatchIn(value)
        while(current.isDefined) {
          val m = current.get
          if (m.start > 0) {
            buf += q"$parent.appendChild(dom.document.createTextNode(${remaining.take(m.start)}))"
          }
          buf += q"$parent.appendChild(dom.document.createTextNode(${args(m.group(1).toInt).toString}))"
          remaining = remaining.drop(m.end)
          current = regex.findFirstMatchIn(value)
        }
        if (remaining.nonEmpty)
          buf += q"$parent.appendChild(dom.document.createTextNode($remaining))"
        buf        
    }
    def applyAttributes(parent: TermName, attribs: scala.xml.MetaData): Iterable[Tree] = attribs.collect {
      case UnprefixedAttribute(key,Text(value),next) =>
        import clide.reactive.Event
        if (value.matches("\\{\\{[0-9]+\\}\\}")) args(value.drop(2).dropRight(2).toInt) match {
          case e: c.Expr[Event[_]] => q"$e.foreach(x => $parent.asInstanceOf[_root_.scala.scalajs.js.Dynamic].${newTermName(key)} = x)" // TODO: unsubscribe on dom deconstruction
          case e => q"$parent.asInstanceOf[_root_.scala.scalajs.js.Dynamic].${newTermName(key)} = $e"
        }         
        else
          q"$parent.setAttribute($key,$value)"
    }
    def createGetterInterfaces(attribs: scala.xml.MetaData): Iterable[Tree] = attribs.collect {
      case PrefixedAttribute("model",name,Text(key),next) =>
        q"""def ${newTermName(name)}(): String"""
      case PrefixedAttribute("event",name,Text(key),next) =>
        val et = key match {
          case _ => tq"_root_.org.scalajs.dom.Event"
        }
        q"""def ${newTermName(name)}(): _root_.clide.reactive.Event[$et]"""
    }
    def createSetterInterfaces(attribs: scala.xml.MetaData): Iterable[Tree] = attribs.collect {
      case PrefixedAttribute("model",name,value,next) =>
        q"""def ${newTermName(name + "_$eq")} (value: String)"""
    }    
    def createGetterImpls(parent: TermName, attribs: scala.xml.MetaData): Iterable[Tree] = attribs.collect {
      case PrefixedAttribute("model",name,Text(key),next) =>
        q"""def ${newTermName(name)}(): String = $parent.asInstanceOf[_root_.scala.scalajs.js.Dynamic].${newTermName(key)}.asInstanceOf[String]"""
      case PrefixedAttribute("event",name,Text(key),next) =>
        val et = key match {
          case _ => tq"_root_.org.scalajs.dom.Event"
        }
        q"""def ${newTermName(name)}(): _root_.clide.reactive.Event[$et] = _root_.clide.reactive.ui.events.DOMEvent($parent,$key)"""
    }
    def createSetterImpls(parent: TermName, attribs: scala.xml.MetaData): Iterable[Tree] = attribs.collect {
      case PrefixedAttribute("model",name,Text(key),next) =>
        q"""def ${newTermName(name + "_$eq")} (value: String) = $parent.asInstanceOf[_root_.scala.scalajs.js.Dynamic].${newTermName(key)} = value"""
    }
    val rootChildren = createChildren(newTermName("parent"), xml.child)   
    val result = q"""{
      import _root_.org.scalajs.dom
      trait ReturnType extends _root_.clide.reactive.ui.InsertedView {
        ..$accessorInterfaces
      }
      new _root_.clide.reactive.ui.Template[ReturnType] {
        def render(context: InsertionContext) = {
          val parent = dom.document.createDocumentFragment()
          ..$rootChildren
          context.insert(parent)
          new ReturnType {
            ..$accessorImpls
            def destroy() {
              println("view destroyed")
            }
          }
        }
      }      
    }"""
    c.Expr[Any](result)
  }
}