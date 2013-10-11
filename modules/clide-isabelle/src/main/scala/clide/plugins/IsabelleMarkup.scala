package clide.plugins

import isabelle._
import scala.collection.SortedMap
import clide.collaboration.{Annotation,Plain,Annotate}

object IsabelleMarkup {  
  def annotations(xml: XML.Tree, c: Option[Map[String,String]] = None): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>
      println("markup: " + markup)
      println("body:   " + body)
      // TODO: use body
      body2.flatMap(annotations(_))
    case XML.Elem(markup, body) =>
      val c2 = markup.name match {
        case Markup.COMMAND => Some(Map("c"->"command"))
        case Markup.KEYWORD  | 
             Markup.KEYWORD1 | 
             Markup.KEYWORD2 => Some(Map("c" -> "keyword"))
        case Markup.STRING  => Some(Map("c" -> "string"))
        case Markup.COMMENT => Some(Map("c" -> "comment"))
        case Markup.BAD | Markup.ERROR => Some(Map("c" -> "error"))
        case Markup.WARNING => Some(Map("c" -> "warning"))
        case Markup.ENTITY  => Some(Map("c" -> "entity"))
        case _              => None
      }
      val n = c.flatMap(c => c2.map(c ++ _)).orElse(c).orElse(c2)      
      body.flatMap(annotations(_,n))
    case XML.Text(content)      => c match {
        case None    => List(Plain(content.length))
        case Some(c) => List(Annotate(content.length,c))
      }      
  }
      
  def annotations(snapshot: Document.Snapshot): List[Annotation] = {
    val xml = snapshot.state.markup_to_XML(snapshot.version, snapshot.node, _ => true)
    xml.flatMap(annotations(_))
  }
}