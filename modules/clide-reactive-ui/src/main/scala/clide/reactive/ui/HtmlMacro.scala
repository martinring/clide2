package clide.reactive

import scala.reflect.macros.Context
import scala.language.experimental.macros
import org.scalajs.dom
import scala.xml._
import org.xml.sax.SAXParseException
import scala.reflect.api.Universe
import scala.collection.mutable.Buffer
import clide.reactive.Event
import scala.annotation.StaticAnnotation
import org.scalajs.dom.HTMLFormElement
import clide.reactive.ui.internal._
import clide.reactive.ui.events._
import scala.concurrent.ExecutionContext

package object ui {
  class view extends StaticAnnotation {
    def macroTransform(annottees: Any*) = macro viewMacroImpl
  }
  
  implicit class HTMLInterpolator(val sc: StringContext) extends AnyVal {
    def html(args: Any*): Any = error("html interpolator may only be called within @view classes")
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
        wiring += atPos(pos)(q"$parent.appendChild(_root_.org.scalajs.dom.document.createTextNode($value))")
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

/*trait Template[+T <: InsertedNode] {
  def render(context: InsertionContext): T
}

object HTMLMacro {
  
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
        var current = regex.findFirstMatchIn(remaining)
        while(current.isDefined) {
          val m = current.get
          if (m.start > 0) {
            buf += q"$parent.appendChild(dom.document.createTextNode(${remaining.take(m.start)}))"
          }
          val arg = args(m.group(1).toInt)
          if (arg.actualType <:< c.typeOf[clide.reactive.Event[_]]) {
            val ic = nextName()            
            buf += q"""var $ic = _root_.clide.reactive.ui.InsertionContext.append($parent).insert(dom.document.createComment("placeholder"))"""
            buf += q"""$arg.foreach { v => $ic.remove(); $ic = v.render($ic.replace) }"""            
          }
          else {
            buf += q"""$parent.appendChild(dom.document.createTextNode(${args(m.group(1).toInt)}.toString))"""
          }
          remaining = remaining.drop(m.end)
          current = regex.findFirstMatchIn(remaining)
        }
        if (remaining.nonEmpty)
          buf += q"$parent.appendChild(dom.document.createTextNode($remaining))"
        buf        
    }
    def applyAttributes(parent: TermName, attribs: scala.xml.MetaData): Iterable[Tree] = attribs.collect {
      case UnprefixedAttribute(key,Text(value),next) =>
        import clide.reactive.Event
        if (value.matches("\\{\\{[0-9]+\\}\\}")) {
          val arg = args(value.drop(2).dropRight(2).toInt)
          if (arg.actualType <:< c.typeOf[clide.reactive.Event[clide.reactive.ui.Template[InsertedNode]]])
            q"$arg.foreach { v => $parent.asInstanceOf[_root_.scala.scalajs.js.Dynamic].${newTermName(key)} = v }" // TODO: unsubscribe on dom deconstruction          
          else 
            q"$parent.asInstanceOf[_root_.scala.scalajs.js.Dynamic].${newTermName(key)} = $arg"
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
      trait ReturnType extends _root_.clide.reactive.ui.InsertedNode {
        ..$accessorInterfaces
      }
      new _root_.clide.reactive.ui.Template[ReturnType] {
        def render(context: InsertionContext) = {
          val parent = dom.document.createDocumentFragment()
          ..$rootChildren
          val first = parent.firstChild
          val last = parent.lastChild
          context.insert(parent)
          new ReturnType {
            ..$accessorImpls
            def remove() = if (first != null) {
              var current = first
              while (current != last) {
                current.parentNode.removeChild(current)
                current = current.nextSibling
              }
              if (current != null)
                current.parentNode.removeChild(current)
            }
            def before =
              _root_.clide.reactive.ui.InsertionContext.before(first)
            def replace = {
              var current = first
              while (current != last) {
                current = current.nextSibling
                current.parentNode.removeChild(current)
              }
              _root_.clide.reactive.ui.InsertionContext.replace(first)         
            }             
          }
        }
      }
    }"""
    c.Expr[Any](result)
  }*/
