package clide.isabelle

import clide.collaboration.Annotate
import clide.collaboration.Annotation
import clide.collaboration.Annotations
import clide.collaboration.Plain
import isabelle.Document
import isabelle.Markup
import isabelle.Symbol
import isabelle.XML
import isabelle.HTML

object IsabelleMarkup {
  def annotations(xml: XML.Tree, c: Option[Map[String,String]] = None): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>      
      markup.name match {        
        case Markup.ERROR | Markup.BAD => 
          body2.flatMap(annotations(_,Some(Map("c"->"error","e"->XML.content(body)))))
        case Markup.WARNING =>
          body2.flatMap(annotations(_,Some(Map("c"->"warning","w"->XML.content(body)))))
        case Markup.WRITELN =>
          body2.flatMap(annotations(_,Some(Map("c"->"writeln","i"->XML.content(body)))))
        case Markup.INFORMATION =>
          body2.flatMap(annotations(_,Some(Map("c"->"info","i"->XML.content(body)))))
        case Markup.TYPING =>
          body2.flatMap(annotations(_,Some(Map("c"->"typing","t"->XML.content(body)))))
        case other =>
          println("unhandled " + other + ": " + body)
          body2.flatMap(annotations(_))
      }                      
    case XML.Elem(markup, body) =>      
      val c2 = markup.name match {
        case Markup.COMMENT => Some(Map("c" -> "comment"))
        case Markup.TFREE => Some(Map("c" -> "tfree"))
        case Markup.BOUND => Some(Map("c" -> "bound"))
        case Markup.FREE => Some(Map("c" -> "free"))
        case Markup.TVAR => Some(Map("c" -> "tvar"))
        case Markup.SKOLEM => Some(Map("c" -> "skolem"))
        case Markup.BAD | Markup.ERROR => Some(Map("c" -> "error"))
        case Markup.WARNING => Some(Map("c" -> "warning"))
        case Markup.ENTITY  => Some(Map("c" -> "entity"))
        case other          => None
      }
      val n = (c,c2) match {
        case (Some(c),Some(c2)) => 
          val cc = (c.get("c"),c2.get("c")) match {
            case (Some(cc),Some(c2c)) => Map("c" -> (cc + " " + c2c))
            case _                    => Map()
          }          
          Some(c ++ c2 ++ cc)
        case (None   ,Some(c2)) => Some(c2)
        case (c,      None)     => c
      }           
      body.flatMap(annotations(_,n))
    case XML.Text(content)      => c match {
        case None    => List(Plain(content.length))
        case Some(c) => List(Annotate(content.length,c))
      }      
  }
      
  def highlighting(header: Document.Node.Header, snapshot: Document.Snapshot): Annotations = {    
    val xml = snapshot.state.markup_to_XML(snapshot.version, snapshot.node, _ => true)
    val xmlAnnons = xml.flatMap(annotations(_))
    val headerErrors = header.errors.map(msg => Annotate(0,Map("e"->msg)))
    (headerErrors ++ xmlAnnons).foldLeft(new Annotations) {
      case (as, Plain(n))      => as.plain(n)
      case (as, Annotate(n,c)) => as.annotate(n, c)
    }
  }
  
  def substitutions(state: String): Annotations =
    Symbol.iterator(state).foldLeft(new Annotations) {
      case (as, sym) if sym.length == 1 || Symbol.decode(sym) == sym =>        
        as.plain(sym.length)
      case (as, sym) =>
        as.annotate(sym.length, Map("c"->"symbol","s"->Symbol.decode(sym)))
    }  
}