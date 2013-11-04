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
  def annotations(xml: XML.Tree, c: Set[(AnnotationType.Value,String)] = Set.empty): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>
      println("marlup:" + markup)
      println("bory: " + body)
      println("body2: " + body2)
      
      markup.name match {        
        case Markup.ERROR | Markup.BAD =>           
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class        -> "error",
              AnnotationType.ErrorMessage -> XML.content(body))))
        case Markup.WARNING =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class          -> "warning",
              AnnotationType.WarningMessage -> XML.content(body))))
        case Markup.WRITELN =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class       -> "writeln",
              AnnotationType.InfoMessage -> XML.content(body))))
        case Markup.INFORMATION =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class       -> "info",
              AnnotationType.InfoMessage -> XML.content(body))))
        case Markup.TYPING =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class   -> "typing",
              AnnotationType.Tooltip -> XML.content(body))))
        case other =>          
          body2.flatMap(annotations(_))
      }
      
    case XML.Elem(markup, body) =>
      val classes = Map(
          Markup.COMMENT -> "comment",
          Markup.TFREE   -> "tfree",
          Markup.BOUND   -> "bound",
          Markup.FREE    -> "free",
          Markup.TVAR    -> "tvar",
          Markup.SKOLEM  -> "skolem",
          Markup.BAD     -> "error",
          Markup.ENTITY  -> "entity")
      
      val c2 = markup.name match {
        case m if classes.isDefinedAt(m) => Set(AnnotationType.Class -> classes(m))
        case other          => Set.empty
      }                 
      
      body.flatMap(annotations(_,c ++ c2))
      
    case XML.Text(content) => c.size match {      
        case 0 => List(Plain(content.length))
        case _ => List(Annotate(content.length,c))
      }      
  }
      
  def highlighting(header: Document.Node.Header, snapshot: Document.Snapshot): Annotations = {
    val anns = snapshot.node.commands.iterator.toList.flatMap { cmd =>           
      val xml = snapshot.state.commands(cmd.id).markup_to_XML(_ => true)
      xml.flatMap(annotations(_))
    }
    println(anns)
    anns.foldLeft(new Annotations) {
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
        as.annotate(sym.length, Set(AnnotationType.Class -> "symbol",AnnotationType.Substitution -> Symbol.decode(sym)))
    }  
}