package clide.reactive

import scala.reflect.macros.Context
import scala.language.experimental.macros
import org.scalajs.dom
import scala.xml._
import org.xml.sax.SAXParseException
import scala.reflect.api.Universe
import scala.collection.mutable.Buffer
import scala.annotation.StaticAnnotation
import org.scalajs.dom.HTMLFormElement
import clide.reactive.ui.internal._
import clide.reactive.ui.events._
import scala.concurrent.ExecutionContext
import reflect.runtime.universe.TypeTag

package object ui {    
  class view extends StaticAnnotation {
    def macroTransform(annottees: Any*) = macro viewMacroImpl
  }

  implicit class HTMLInterpolator(val sc: StringContext) extends AnyVal {
    def html(args: Any*): Any = sys.error("html interpolator may only be called within @view classes")
  }

  implicit class RichHTMLElement(val elem: dom.HTMLElement) extends AnyVal {
    def appendChild(text: String): Unit = elem.appendChild(dom.document.createTextNode(text))
    def appendChild(event: Event[String])(implicit ec: ExecutionContext): Unit = {
      val textNode = elem.appendChild(dom.document.createTextNode(""))
      event.foreach(textNode.textContent = _).foreach(_ => textNode.parentNode.removeChild(textNode))
    }
    def appendChild(event: Event[dom.Node])(implicit ec: ExecutionContext, evidence: TypeTag[dom.Node]): Unit = {
      var node = elem.appendChild(dom.document.createComment("placeholder"))
      event.foreach(node.parentNode.replaceChild(_, node)).foreach(_ => node.parentNode.removeChild(node))
    }
    /*def appendChild(event: Event[InsertionContext => Cancellable])(implicit ec: ExecutionContext): Unit = {
      var insert = InsertionContext.replace(elem.appendChild(dom.document.createComment("placeholder")))      
      var cancel = Cancellable()
      event.foreach { c =>
        cancel()
      }
    }*/
  }
  
  implicit class HTMLEvents(val elem: dom.HTMLInputElement) extends AnyVal {
    def textChange(implicit ec: ExecutionContext): Event[String] = DOMEvent(elem,"input").sample(elem.value)
  }

  def viewMacroImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val param = annottees.map(_.tree).toList.headOption

    val (viewName, args, members) = param match {
      case Some(q"class $name(..$args) { ..$members }") =>
        (name,args,members)
      case _ =>
        c.abort(c.enclosingPosition, "@view must be applied to a class declaration")
    }

    var counter = 0
    def nextElemName() = {
      counter += 1
      newTermName("$elem_" + counter)
    }

    val fragment = newTermName("$rootFragment")
    val elemDecls = Buffer.empty[Tree]
    val wiring = Buffer.empty[Tree]

    elemDecls += q"private lazy val $fragment = _root_.org.scalajs.dom.document.createDocumentFragment()"

    def getValue(pos: Position, value: String, args: List[Tree]): Tree = 
      if (value.startsWith("{{") && value.endsWith("}}"))
        args(value.drop(2).dropRight(2).toInt)
      else
        q"$value"

    def processAttributes(parent: TermName, pos: Position, md: MetaData, args: List[Tree]): Unit = md.foreach {
      case UnprefixedAttribute(key,Text(value),next) =>
        val keyName = newTermName(key match {
          case "class" => "className"          
          case other => other
        })
        wiring += atPos(pos)(q"$parent.$keyName = ${getValue(pos,value,args)}")
      case PrefixedAttribute(prefix,key,Text(value),next) if prefix != "scala" =>
        val oName = newTermName(prefix)
        val kName = newTermName(key)
        if (value.startsWith("@"))
          wiring += atPos(pos)(q"def ${newTermName(key + "_$eq")}(value: String) = $oName.$kName($parent,value)")
        else
          wiring += atPos(pos)(q"$oName.$kName($parent,${getValue(pos,value,args)})")
      case PrefixedAttribute("scala",key,Text(value),next) =>
        if (key != "name")
          c.abort(pos, "unsupported directive: scala:" + key)
    }

    def processTree(parent: TermName, pos: Position, xml: NodeSeq, args: List[Tree]): Unit = xml.foreach {
      case Elem(prefix, label, attribs, scope, child @ _*) =>
        val name = attribs.find(_.prefixedKey == "scala:name")
                              .map(md => newTermName(md.value.toString))
                              .getOrElse(nextElemName())
        if (prefix != null)
          elemDecls += atPos(pos)(q"protected lazy val $name = new ${newTermName(prefix)}.${newTermName(label)}")
        else {
          val elemType = HTMLTagTypes(label)(c)(pos).getOrElse(c.abort(pos, "unknown html5 tag: " + label))
          elemDecls += atPos(pos)(q"protected lazy val $name: $elemType = _root_.org.scalajs.dom.document.createElement($label).asInstanceOf[$elemType]")
        }
        processAttributes(name, pos, attribs, args)
        wiring += atPos(pos)(q"$parent.appendChild($name)")
        processTree(name, pos, child, args)
      case Text(value) =>
        val regex = "\\{\\{([0-9]+)\\}\\}".r
        var remaining = value
        var current = regex.findFirstMatchIn(remaining)
        while (current.isDefined) {
          wiring += atPos(pos)(q"$parent.appendChild(${remaining.take(current.get.start)})")
          wiring += atPos(pos)(q"$parent.appendChild(${args(current.get.group(1).toInt)})")
          remaining = remaining.drop(current.get.end)
          current = regex.findFirstMatchIn(remaining)
        }
        wiring += atPos(pos)(q"$parent.appendChild($remaining)")
      case other => c.warning(pos, "html skipped: " + other)
    }

    members.foreach {
      case html@q"StringContext(..$parts).html(..$args)" =>
        val builder = new StringBuilder
        if (parts.nonEmpty) {
          builder.append(parts.head.asInstanceOf[Literal].value.value.asInstanceOf[String])
          var pos = 0
          while (pos + 1 < parts.length) {
            builder.append("{{").append(pos.toString).append("}}")
            pos += 1
            builder.append(parts(pos).asInstanceOf[Literal].value.value.asInstanceOf[String])
          }
        }
        val xmlTree = try {
          xml.XML.loadString(builder.result())
        } catch {
          case e: SAXParseException =>
            c.abort(parts(0).pos.focus, e.getMessage())
        }
        processTree(fragment, html.pos, xmlTree, args)
      case other: DefDef if other.name.decoded != "<init>" =>
        wiring += other
      case other: ValDef =>
        wiring += other
      case _ => //
    }

    c.Expr(q"""
      class ${viewName}(..$args)(implicit context: _root_.clide.reactive.ui.InsertionContext) {
        ..$elemDecls
        ..$wiring
        context.insert($fragment)
      }""")
  }
}