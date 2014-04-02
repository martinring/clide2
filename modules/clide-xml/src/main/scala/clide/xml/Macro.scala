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
  def inline[S](schema: S, xmlCode: String) = macro inlineMacro
  def include[S](schema: S, path: String) = macro includeMacro
  
  def includeMacro(c: Context)(schema: c.Expr[Any], path: c.Expr[String]): c.Expr[Any] = {
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
    
    expand(c)(path.tree.pos,schema,xmlTree)
  }
  
  def inlineMacro(c: Context)(schema: c.Expr[Any], xmlCode: c.Expr[String]): c.Expr[Any] = {
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
   
    expand(c)(xmlCode.tree.pos, schema,xmlTree)
  }
  
  
  private def expand(c: Context)(pos: c.Position, schema: c.Expr[Any], xml: scala.xml.Elem): c.Expr[Any] = {
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
                                              .map(m => m.name.decoded -> m.asMethod)
                                              .toMap
                                              
    val tagConstructors = schema.actualType.members.filter(_.isClass)
                                                   .map(_.asClass)
                                                   .filter(_.isCaseClass)
                                                   .map(m => m.name.decoded -> m.companionSymbol.typeSignature.members.find(_.name.decoded == "apply").get.asMethod)
    
    val tags = tagMethods ++ tagConstructors
                                              
    val regex = "\\{[^\\}]*\\}".r
    
    def getValues(v: String): List[String] = {      
      val buf = Buffer.empty[String]
      var remaining = v
      if (remaining.isEmpty()) {
        Nil
      } else {
	      var current = regex.findFirstMatchIn(remaining)
	      while (current.isDefined) {
	        val cur = current.get	       
	        if (cur.start > 0)
	          buf += Literal(Constant(remaining.take(cur.start))).toString
	        buf += cur.matched
	        remaining = remaining.drop(cur.end)
	        current = regex.findFirstMatchIn(remaining)
	      }
	      Literal(Constant(""))
	      
	      if (remaining.nonEmpty)
	        buf += Literal(Constant(remaining)).toString
	      buf.toList
      }
    }
    
    def createNode(node: scala.xml.Node, parent: Option[TermName] = None, code: Buffer[Tree] = code): Option[TermName] = node match {
      case elem@scala.xml.Elem(prefix,label,attribs,scope,child@_*) =>
        val name = attribs.find(_.prefixedKey == "scala:name").map(a => newTermName(a.value.text)).getOrElse(c.fresh(newTermName(label + "$")))
        
        attribs.find(_.prefixedKey == "scala:for") match {
          case Some(attrib) =>
            val parts = attrib.value.text.split(":").toList
            if (parts.length != 2)
              c.abort(pos, "malformed scala:for. must be of form 'var:container'")
            val localVar = newTermName(parts.head)
            val collection = c.parse(parts.last)
            collection.pos = pos
            val innerCode = Buffer.empty[Tree]
            val innerRoot = createNode(scala.xml.Elem(prefix,label,attribs.filter(_.prefixedKey != "scala:for"),scope,true,child :_*), None, innerCode).get
            code += atPos(pos)(q"lazy val $name = for ($localVar <- $collection) yield { ..$innerCode; $innerRoot }")
          case None =>
		        val tagMethod = tags.get(label).getOrElse(c.abort(pos, "schema doesn't support element type `" + label + "`"))
		        val allParams = tagMethod.paramss.flatten.map(_.name.decoded)
		        val requiredParams = tagMethod.paramss.flatten.filter(!_.isImplicit).map(_.name.decoded)
		
		        val (params,otherAttribs) = attribs.partition(attrib => attrib.isPrefixed == false && allParams.contains(attrib.key))
		
		        val unset = requiredParams.toSet -- params.map(_.key).toSet
		
		        if (unset.size > 0) {
		          unset.foreach { u =>
		            c.error(pos, "attribute `" + u + "` on element `" + label + "` is required!")
		          }
		          c.abort(pos, "can not initialize element " + label)
		        }
		
		        val paramss = tagMethod.paramss.map(x => x.collect{ 
		          case p if params.exists(_.key == p.name.decoded) => 
		            val result = c.parse(getValues(params.find(_.key == p.name.decoded).get.value.text).mkString(" + "))
		            result.pos = pos
		            result
		        })
		
		        code += atPos(pos)(q"lazy val $name = $schemaName.${newTermName(label)}(...$paramss)")
		
		        otherAttribs.foreach {
		          case attr@UnprefixedAttribute(key,scala.xml.Text(value),next) =>
		            val access = (key).split('.').foldLeft(atPos(pos)(q"$name"): Tree) { case (l, r) => atPos(pos)(Select(l,newTermName(r))) }
		            val values = getValues(value).map{ v => 
		              val result = c.parse(v)
		              result.pos = pos
		              result
		            }
		            if (values.length == 1)
		              code += atPos(pos)(q"$access = ${values.head}")
		            else
		              code += atPos(pos)(q"$access = Seq(..$values)")
		          case attr@PrefixedAttribute(prefix,key,scala.xml.Text(value),next) if prefix != "scala" =>            
		            val access = (key).split('.').foldLeft(atPos(pos)(q"${newTermName(prefix)}"): Tree) { case (l,r) => atPos(pos)(Select(l,newTermName(r))) }
		            val values = c.parse(value).duplicate
		            values.pos = pos
		            code += atPos(pos)(q"$access($name,$values)")
		          case attr@PrefixedAttribute(prefix,key,scala.xml.Text(value),next) if prefix == "scala" =>
		            if (key == "name") ()
		            else c.abort(pos, "unsupported macro directive: " + attr.prefixedKey)
		        }
		
		        child.foreach { e =>
		           createNode(e, Some(name), code)
		        }
        }
		
        parent.foreach { parent =>
          code += atPos(pos)(q"$parent += $name")
        }        
        
		    Some(name)
		    
      case scala.xml.Text(value) =>
        parent.foreach { parent =>
          getValues(value).foreach { value =>
            val cd = c.parse(value)
            cd.pos = pos
            code += atPos(pos)(q"$parent += $cd")
          }
        }

        None
    }    

    createNode(xml) match {
      case Some(rootElem) =>
        val result = q"..$code; $rootElem"
        c.Expr(atPos(pos)(q"..$code; $rootElem"))
      case None =>
        c.abort(c.enclosingPosition,"no valid root element")
    }
  }
}