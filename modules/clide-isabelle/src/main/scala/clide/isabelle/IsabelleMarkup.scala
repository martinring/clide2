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
import clide.collaboration.AnnotationType

object IsabelleMarkup {
  def annotations(xml: XML.Tree, c: Option[Map[AnnotationType.Value,String]] = None): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>      
      markup.name match {        
        case Markup.ERROR | Markup.BAD => 
          body2.flatMap(annotations(_,Some(Map(
              AnnotationType.Class        -> "error",
              AnnotationType.ErrorMessage -> XML.content(body)))))
        case Markup.WARNING =>
          body2.flatMap(annotations(_,Some(Map(
              AnnotationType.Class          -> "warning",
              AnnotationType.WarningMessage -> XML.content(body)))))
        case Markup.WRITELN =>
          body2.flatMap(annotations(_,Some(Map(
              AnnotationType.Class       -> "writeln",
              AnnotationType.InfoMessage -> XML.content(body)))))
        case Markup.INFORMATION =>
          body2.flatMap(annotations(_,Some(Map(
              AnnotationType.Class       -> "info",
              AnnotationType.InfoMessage -> XML.content(body)))))
        case Markup.TYPING =>
          body2.flatMap(annotations(_,Some(Map(
              AnnotationType.Class   -> "typing",
              AnnotationType.Tooltip -> XML.content(body)))))
        case other =>          
          body2.flatMap(annotations(_))
      }
      
    case XML.Elem(markup, body) =>      
      val c2 = markup.name match {
        case Markup.COMMENT => Some(Map(AnnotationType.Class -> "comment"))
        case Markup.TFREE => Some(Map(AnnotationType.Class -> "tfree"))
        case Markup.BOUND => Some(Map(AnnotationType.Class -> "bound"))
        case Markup.FREE => Some(Map(AnnotationType.Class -> "free"))
        case Markup.TVAR => Some(Map(AnnotationType.Class -> "tvar"))
        case Markup.SKOLEM => Some(Map(AnnotationType.Class -> "skolem"))
        case Markup.BAD | Markup.ERROR => Some(Map(AnnotationType.Class -> "error"))
        case Markup.WARNING => Some(Map(AnnotationType.Class -> "warning"))
        case Markup.ENTITY  => Some(Map(AnnotationType.Class -> "entity"))
        case other          => None
      }
      val n = (c,c2) match {
        case (Some(c),Some(c2)) => 
          val cc = (c.get(AnnotationType.Class),c2.get(AnnotationType.Class)) match {
            case (Some(cc),Some(c2c)) => Map(AnnotationType.Class -> (cc + " " + c2c))
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
    val headerErrors = header.errors.map(msg => Annotate(0,Map(AnnotationType.ErrorMessage->msg)))
    (headerErrors ++ xmlAnnons).foldLeft(new Annotations) {
      case (as, Plain(n))      => as.plain(n)
      case (as, Annotate(n,c)) => as.annotate(n, c)
    }
  }
  
  def output(snapshot: Document.Snapshot): Annotations = {
    snapshot.state.commands.map { case (id, cmd) =>      
      cmd.results.entries.foreach { println }
    }    
    new Annotations
  }
  
  def substitutions(state: String): Annotations =
    Symbol.iterator(state).foldLeft(new Annotations) {
      case (as, sym) if sym.length == 1 || Symbol.decode(sym) == sym =>        
        as.plain(sym.length)
      case (as, sym) =>
        as.annotate(sym.length, Map(AnnotationType.Class -> "symbol",AnnotationType.Substitution -> Symbol.decode(sym)))
    }  
}