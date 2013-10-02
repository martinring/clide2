package clide.plugins

import isabelle._
import scala.collection.SortedMap

object IsabelleMarkup {
  def getStates(
    snapshot: Document.Snapshot,
    ranges: Vector[(Int, Int)]) = ranges.map {
    case (start, end) =>
      type T = (Protocol.Status, Int)
      val f: PartialFunction[(T, Text.Info[XML.Elem]), T] = {
        case ((status, p), Text.Info(_, XML.Elem(markup, _))) =>
          if (markup.name == Markup.WARNING) (status, p max 1)
          else if (markup.name == Markup.ERROR) (status, p max 2)
          else (Protocol.command_status(status, markup), p)
      }
      val results = snapshot.cumulate_markup[(Protocol.Status, Int)](
        Text.Range(start, end),
        (Protocol.Status.init, 0),
        Some(Protocol.command_status_markup + Markup.WARNING + Markup.ERROR),
        _ => f)
      if (results.isEmpty) "init"
      else {
        val (status, p) = ((Protocol.Status.init, 0) /: results) {
          case ((s1, p1), Text.Info(_, (s2, p2))) => (s1 + s2, p1 max p2)
        }
        if (p == 1) "warning"
        else if (p == 2) "error"
        else if (status.is_unprocessed) "unprocessed"
        else if (status.is_running) "running"
        else if (status.is_failed) "failed"
        else "finished"
      }
  }
  
  def getLineMessages(
    snapshot: Document.Snapshot,
    ranges: Vector[(Int, Int)]) = ranges.map {
    case (start, end) =>
      type T = (Protocol.Status, Int)
      val f: PartialFunction[(T, Text.Info[XML.Elem]), T] = {
        case ((status, p), Text.Info(_, XML.Elem(markup, _))) =>
          if (markup.name == Markup.WARNING) (status, p max 1)
          else if (markup.name == Markup.ERROR) (status, p max 2)
          else (Protocol.command_status(status, markup), p)
      }
      val results = snapshot.cumulate_markup[(Protocol.Status, Int)](
        Text.Range(start, end),
        (Protocol.Status.init, 0),
        Some(Protocol.command_status_markup + Markup.WARNING + Markup.ERROR),
        _ => f)
      if (results.isEmpty) "init"
      else {
        val (status, p) = ((Protocol.Status.init, 0) /: results) {
          case ((s1, p1), Text.Info(_, (s2, p2))) => (s1 + s2, p1 max p2)
        }
        if (p == 1) "warning"
        else if (p == 2) "error"
        else if (status.is_unprocessed) "unprocessed"
        else if (status.is_running) "running"
        else if (status.is_failed) "failed"
        else "finished"
      }
  }

  import Markup._
  val outer = Set(COMMAND,KEYWORD,OPERATOR,CONTROL,BAD,ERROR,WARNING)
        
  val inner = Set(TVAR,FREE,SORT,TYP,TERM,PROP,ML_TYPING,TOKEN_RANGE,ENTITY,
      ERROR,WARNING,
      TYPING,FREE,SKOLEM,BOUND,VAR,TFREE,TVAR,ML_SOURCE,DOCUMENT_SOURCE,ML_KEYWORD)
  
  def tooltip_message(snapshot: Document.Snapshot, range: Text.Range): Option[String] =
  {
    val msgs =
      snapshot.cumulate_markup[SortedMap[Long, String]](range, SortedMap.empty,
        Some(Set(Markup.WRITELN, Markup.WARNING, Markup.ERROR)),
        _ => {
          case (msgs, Text.Info(_, msg @ XML.Elem(Markup(markup, Markup.Serial(serial)), _)))
          if markup == Markup.WRITELN ||
              markup == Markup.WARNING ||
              markup == Markup.ERROR =>
            msgs + (serial ->
              Pretty.string_of(List(msg), margin = 40))
        }).toList.flatMap(_.info)
    if (msgs.isEmpty) None else Some(cat_lines(msgs.iterator.map(_._2)))
  }        
     
  private val tooltips: Map[String, String] =
    Map(
      Markup.SORT -> "sort",
      Markup.TYP -> "type",
      Markup.TERM -> "term",
      Markup.PROP -> "proposition",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable",
      Markup.SKOLEM -> "skolem variable",
      Markup.BOUND -> "bound variable",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable",
      Markup.ML_SOURCE -> "ML source",
      Markup.DOCUMENT_SOURCE -> "document source")

  private val tooltip_elements =
    Set(Markup.ENTITY, Markup.TYPING, Markup.ML_TYPING) ++
    tooltips.keys

  private def string_of_typing(kind: String, body: XML.Body): String =
    Pretty.string_of(List(Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)),
      margin = 40)

  def tooltip(snapshot: Document.Snapshot, range: Text.Range): Option[String] =
  {
    def add(prev: Text.Info[List[(Boolean, String)]], r: Text.Range, p: (Boolean, String)) =
      if (prev.range == r) Text.Info(r, p :: prev.info) else Text.Info(r, List(p))

    val tips =
      snapshot.cumulate_markup[Text.Info[(List[(Boolean, String)])]](
        range, Text.Info(range, Nil), Some(tooltip_elements),
        _ => {
          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _))) =>
            add(prev, r, (true, kind + " " + quote(name)))
          case (prev, Text.Info(r, XML.Elem(Markup(Markup.TYPING, _), body))) =>
            add(prev, r, (true, string_of_typing("::", body)))
          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            add(prev, r, (false, string_of_typing("ML:", body)))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _)))
          if tooltips.isDefinedAt(name) => add(prev, r, (true, tooltips(name)))
        }).toList.flatMap(_.info.info)

    val all_tips =
      (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
    if (all_tips.isEmpty) None else Some(cat_lines(all_tips))
  }

  
  def getTokens(
    snapshot: Document.Snapshot,
    ranges: Vector[(Int, Int)]) = ranges.map {
    case (start, end) =>
      def add(stream: Stream[Text.Info[List[String]]], set: Set[String]) = stream.map {
      case info => 
        val r = snapshot.cumulate_markup[List[String]](
          info.range, 
          List("text"), 
          Some(set),
          _ => { case (x, m) => List(m.info.markup.name) })
        Text.Info(info.range, info.info ++ (r.foldLeft[List[String]](Nil){ case (a,b) => a ++ b.info }))
      }
            
      val fine = snapshot.cumulate_markup[List[String]](
        Text.Range(start,end),
        Nil,
        Some(inner),
        _ => { case (x, m) => List(m.info.markup.name) })
   
      fine
  }
}