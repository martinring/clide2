package clide.plugins

import isabelle._
import scala.collection.SortedMap

object IsabelleMarkup { 
  private val textClasses: Map[String, Option[String]] = Map(
      Markup.KEYWORD1 -> "cm-keyword",
      Markup.KEYWORD2 -> "cm-keyword",
      Markup.STRING -> "cm-string",
      Markup.ALTSTRING -> "cm-string",
      Markup.VERBATIM -> "cm-verbatim",
      Markup.LITERAL -> "cm-literal",
      Markup.DELIMITER -> "cm-delimiter",
      Markup.TFREE -> "cm-tfree",
      Markup.TVAR -> "cm-tvar",
      Markup.FREE -> "cm-free",
      Markup.SKOLEM -> "cm-skolem",
      Markup.BOUND -> "cm-bound",
      Markup.VAR -> "cm-variable",
      Markup.INNER_STRING -> "cm-inner-string",
      Markup.INNER_COMMENT -> "cm-inner-comment",
      Markup.DYNAMIC_FACT -> "cm-dynamic",
      Markup.ML_KEYWORD -> "cm-keyword",
      Markup.ML_DELIMITER -> "cm-delimiter",
      Markup.ML_NUMERAL -> "cm-num",
      Markup.ML_CHAR -> "cm-string",
      Markup.ML_STRING -> "cm-string",
      Markup.ML_COMMENT -> "cm-comment",
      Markup.ANTIQ -> "cm-quote").mapValues(Some.apply _)

  def textClass(snapshot: Document.Snapshot, range: Text.Range)
      : Stream[Text.Info[Option[String]]] =
  {
    snapshot.cumulate_markup(range, None, Some(textClasses.keySet), _ =>
    { case (_, Text.Info(_, XML.Elem(Markup(m, _), _))) if textClasses.isDefinedAt(m) => textClasses(m) })
  }
}