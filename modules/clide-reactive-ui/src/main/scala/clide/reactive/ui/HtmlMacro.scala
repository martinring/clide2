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
import clide.reactive.ui.events._
import scala.concurrent.ExecutionContext
import reflect.runtime.universe.TypeTag
import java.io.FileNotFoundException

package object ui {
  def include(path: String) = ???
  
  def htmlMacroImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._ 
    val path = annottees.head match {
      case Literal(Constant(pathLit: String)) => pathLit        
      case _ => c.abort(annottees.head.tree.pos, "@include must be followed by a string literal")
    }
    c.abort(c.enclosingPosition, "loading: " + path)    
  }
  
  class view extends StaticAnnotation {
    def macroTransform(annottees: Any*) = macro viewMacroImpl
  }

  implicit class HTMLInterpolator(val sc: StringContext) extends AnyVal {
    def html(args: Any*): Any = ???
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
    val unwiring = Buffer.empty[Tree]
    val interface = Buffer.empty[Tree]
    
    elemDecls += q"private lazy val $fragment = _root_.org.scalajs.dom.document.createDocumentFragment()"

    def getValue(pos: Position, value: String, args: List[Tree]): Tree = 
      if (value.startsWith("{{") && value.endsWith("}}"))
        args(value.drop(2).dropRight(2).toInt)
      else
        q"$value"

    def processAttributes(parent: TermName, pos: Position, md: MetaData, args: List[Tree]): Unit = md.foreach {
      case UnprefixedAttribute(key,Text(value),next) =>                
        if (value.startsWith("@")) {
          wiring += atPos(pos)(q"def ${newTermName(value.drop(1) + "_$eq")}(value: String) = $parent.${newTermName(key + "_$eq")}(value)")
          interface += atPos(pos)(q"def ${newTermName(value.drop(1) + "_$eq")}(value: String): Unit")
        } else {
          val l = (key + "_$eq").split('.').foldLeft(q"$parent": Tree)((l,r) => q"$l.${newTermName(r)}")
          wiring += atPos(pos)(q"$l(${getValue(pos,value,args)})")
        }
      case PrefixedAttribute(prefix,key,Text(value),next) if prefix != "scala" =>
        val oName = newTermName(prefix)
        val kName = newTermName(key)
        if (value.startsWith("@")) {
          wiring += atPos(pos)(q"def ${newTermName(value.drop(1) + "_$eq")}(value: String) = $oName.$kName($parent,value)")
          interface += atPos(pos)(q"def ${newTermName(value.drop(1) + "_$eq")}(value: String): Unit")
        } else
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
        if (prefix != null) {
          elemDecls += atPos(pos)(q"protected lazy val $name = ${newTermName(prefix)}.${newTermName(label)}()")
        } else {
          elemDecls += atPos(pos)(q"protected lazy val $name = ${newTermName(label)}()")
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
            c.abort(html.pos, e.getMessage())
        }
        processTree(fragment, html.pos, xmlTree, args)
      case q"$xml: $t" if t.tpe =:= c.typeOf[scala.xml.Elem] =>
        c.abort(xml.pos, "xml!")
      case other@q"def $name(..$params): $t = $body" if name.decoded != "<init>" =>
        interface += q"def $name(..$params): $t"
        wiring += other
      case other: DefDef if other.name.decoded != "<init>" =>
        wiring += other
      case imp: Import =>
        elemDecls += imp
      case other: ValDef =>
        wiring += other
      case q"include($pathLit)" => pathLit match {
        case Literal(Constant(path: String)) =>
          val html = Option(this.getClass().getResourceAsStream(path)).getOrElse {
            c.abort(pathLit.pos, "Invalid resource path")
          }
          c.warning(pathLit.pos, path)
        case _ =>
          c.abort(pathLit.pos, "string literal required here")
      }
      case q"<" =>
        c.warning(params.head.pos, params.head.toString)
      case other => c.warning(other.pos, "skipped: " + other.toString)
    }

    c.Expr(q"""
      trait $viewName extends View {
        ..$interface
      }
      object ${newTermName(viewName.decoded)} {
        def apply(..$args): $viewName = new $viewName {
          ..$elemDecls
          ..$wiring
          var $$inserted = false
          def apply(context: InsertionContext): InsertedNode = {
            if ($$inserted) sys.error(${viewName.decoded} + " may only be inserted once!")
            $$inserted = true
            context.insert($fragment)
          }
        }
      }""")
  }
}