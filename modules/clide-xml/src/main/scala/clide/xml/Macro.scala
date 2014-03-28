package clide.xml

import scala.reflect.macros.Context
import scala.language.experimental.macros
import scala.collection.mutable.StringBuilder
import org.xml.sax.SAXParseException
import scala.collection.mutable.Buffer
import scala.xml.UnprefixedAttribute
import java.io.FileNotFoundException
import scala.xml.PrefixedAttribute

object XML {
  def literal[S](schema: S, xmlCode: String)(body: Unit = {}) = macro inlineMacro
  def include[S](schema: S, path: String)(body: Unit = {}) = macro includeMacro
    
  def includeMacro(c: Context)(schema: c.Expr[Any], path: c.Expr[String])(body: c.Expr[Unit]): c.Expr[Any] = {
    import c.universe._
    
    val pathString = path.tree match {
      case Literal(Constant(value: String)) => value
      case _ => c.abort(path.tree.pos, "path must be specified as a string literal")
    }
    
    val xmlFile = new java.io.File(c.enclosingUnit.source.file.file.getParentFile(),pathString) 
    
    // parse as xml
    val xmlTree = try {
      scala.xml.XML.loadFile(xmlFile)
    } catch {
      case e: FileNotFoundException =>
        c.abort(path.tree.pos, e.getMessage())
      case e: SAXParseException =>       
        c.abort(path.tree.pos, s"[${e.getLineNumber()}:${e.getColumnNumber()}]: ${e.getMessage()}")
    }
    
    expand(c)(path.tree.pos,schema,xmlTree,body)
  }
  
  def inlineMacro(c: Context)(schema: c.Expr[Any], xmlCode: c.Expr[String])(body: c.Expr[Unit]): c.Expr[Any] = {
    import c.universe._

    //put '{0}' '{1}' ... placeholders betweeen parts
    val xmlString = xmlCode.tree match {
      case Literal(Constant(value: String)) => value
    }
    
    val xmlLines = xmlString.split("\n")

    // parse as xml
    val xmlTree = try {
      scala.xml.XML.loadString(xmlString)
    } catch {
      case e: SAXParseException =>       
        c.abort(c.enclosingPosition, e.getMessage())
    }
   
    expand(c)(xmlCode.tree.pos, schema,xmlTree,body)
  }
  
  
  private def expand(c: Context)(pos: c.Position, schema: c.Expr[Any], xml: scala.xml.Elem, body: c.Expr[Unit]): c.Expr[Any] = {
    import c.universe._
    
    // transform into scala code
    val code = Buffer.empty[Tree]
    
    val schemaName = c.fresh(newTermName("schema"))
    
    code += atPos(schema.tree.pos)(q"val $schemaName = $schema")
    code += atPos(schema.tree.pos)(q"import $schemaName._")
    
    val tagMethods = schema.actualType.members.filter(_.isMethod)
                                              .filter(_.isPublic)                    
                                              .filterNot(x => x.owner.isClass && x.owner.asClass.toType =:= c.typeOf[Any])
                                              .filterNot(x => x.owner.isClass && x.owner.asClass.toType =:= c.typeOf[Object])
                                              .filterNot(_.isImplicit)
                                              .map(m => m.name.decoded -> m.asMethod.paramss.headOption.toList.flatten.map(_.name.decoded))
                                              .toMap
    
    val regex = "\\{[^\\}]*\\}".r
    
    def getValues(v: String): List[String] = {      
      val buf = Buffer.empty[String]
      var remaining = v.trim()
      if (remaining.isEmpty()) {
        Nil
      } else {
	      var current = regex.findFirstMatchIn(remaining)
	      while (current.isDefined) {
	        val c = current.get
	        if (c.start > 0)
	          buf += s""""${remaining.take(c.start).replace("\"", "\\\"")}""""
	        buf += c.matched
	        remaining = remaining.drop(c.end)
	        current = regex.findFirstMatchIn(remaining)
	      }
	      if (remaining.nonEmpty)
	        buf += s""""$remaining""""
	      buf.toList
      }
    }
    
    def createNode(node: scala.xml.Node, parent: Option[TermName] = None): Option[TermName] = node match {
      case scala.xml.Elem(prefix,label,attribs,scope,child@_*) =>
        val name = c.fresh(newTermName(label))
        val requiredParams = tagMethods.get(label).getOrElse(c.abort(pos, "schema doesn't support element type `" + label + "`"))

        val (req,otherAttribs) = attribs.partition(attrib => attrib.isPrefixed == false && requiredParams.contains(attrib.key))

        val unset = requiredParams.toSet -- req.map(_.key).toSet
        if (unset.size > 0) {
          unset.foreach { u =>
            c.error(pos, "attribute `" + u + "` on element `" + label + "` is required!")
          }
          c.abort(pos, "can not initialize element " + label)
        }

        val params = requiredParams.map(p => atPos(pos)(c.parse(getValues(req.find(_.key == p).get.value.text).mkString(" + "))))

        code += atPos(pos)(q"lazy val $name = $schemaName.${newTermName(label)}(..$params)")

        otherAttribs.foreach {
          case attr@UnprefixedAttribute(key,scala.xml.Text(value),next) =>
            val access = key.split('.').mkString("`", "`.`", "`")
            code += atPos(pos)(c.parse("`" + name.decoded + "`." + access + " = " + getValues(value).mkString(" + ")))
          case attr@PrefixedAttribute(prefix,key,scala.xml.Text(value),next) =>
            val access = (schemaName.decoded + "." + prefix + '.' + key).split('.').mkString("`", "`.`", "`")
            code += atPos(pos)(c.parse(access + "(" + name.decoded + "," + getValues(value).mkString(" + ") + ")"))
        }
        
        child.foreach { e =>            
           createNode(e, Some(name))
        }
        
        parent.foreach { parent =>
          code += atPos(pos)(q"$parent += $name")
        }
        
        Some(name)
        
      case scala.xml.Text(value) =>
        parent.foreach { parent =>
          getValues(value).foreach { value =>
            code += atPos(pos)(q"$parent += ${atPos(pos)(c.parse(value))}")
          }
        }
        
        None
    }
    
    val b = body.tree match {
      case block: Block =>
        block.children.map(tree => atPos(tree.pos)(c.parse(tree.toString)))        
      case other => List(atPos(other.pos)(c.parse(other.toString)))
    }

    createNode(xml) match {
      case Some(rootElem) =>
        c.Expr(q"""..$code; ..$b; $rootElem""")
      case None =>
        c.abort(c.enclosingPosition,"no root element")
    }
  }
}