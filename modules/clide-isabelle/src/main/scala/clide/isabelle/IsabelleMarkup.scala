package clide.isabelle

import clide.collaboration.Annotate
import clide.collaboration.Annotation
import clide.collaboration.Annotations
import clide.collaboration.Plain
import isabelle.Document
import isabelle.Markup
import isabelle.Symbol
import isabelle.XML

object IsabelleMarkup {
  def annotations(xml: XML.Tree, c: Option[Map[String,String]] = None): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>
      markup.name match {
        case Markup.ERROR | Markup.BAD =>
          Annotate(0,Map("e"->XML.content(body))) :: body2.flatMap(annotations(_))
        case Markup.WARNING =>
          Annotate(0,Map("w"->XML.content(body))) :: body2.flatMap(annotations(_))
        case Markup.WRITELN =>
          Annotate(0,Map("i"->XML.content(body))) :: body2.flatMap(annotations(_))
        case Markup.TYPING =>
          Annotate(0,Map("t"->XML.content(body))) :: body2.flatMap(annotations(_))
        case other =>
          println("unhandled " + other + ": " + body)
          body2.flatMap(annotations(_))
      }                      
    case XML.Elem(markup, body) =>      
      val c2 = markup.name match {
        case Markup.COMMAND => Some(Map("c"->"command"))
        case Markup.KEYWORD  | 
             Markup.KEYWORD1 | 
             Markup.KEYWORD2 => Some(Map("c" -> "keyword"))
        case Markup.
        case Markup.STRING  => Some(Map("c" -> "string"))
        case Markup.COMMENT => Some(Map("c" -> "comment"))
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