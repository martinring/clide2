package clide.plugins

import isabelle._
import scala.collection.SortedMap

object IsabelleMarkup {
  import Markup._
  
  val inner = Set(TVAR,FREE,SORT,TYP,TERM,PROP,ML_TYPING,TOKEN_RANGE,ENTITY,
      KEYWORD, COMMAND, TYPING,FREE,SKOLEM,BOUND,VAR,TFREE,TVAR,ML_SOURCE,
      DOCUMENT_SOURCE, ML_KEYWORD)
  
  def getTokens(snapshot: Document.Snapshot,range: Text.Range) = {                
    snapshot.cumulate_markup[List[String]](
      range,
      Nil,
      Some(inner),
      _ => { case (x, m) => List(m.info.markup.name) })   
  }
  
  def getMessages(snapshot: Document.Snapshot,range: Text.Range) = {
    snapshot.cumulate_markup[List[(String,String)]](
      range,Nil,Some(Set(ERROR,WARNING,BAD)),
      _ => { case (x, m) => List("e" -> m.info.toString) })
  }
}