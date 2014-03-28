/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */

package clide.isabelle

import clide.collaboration.Annotate
import clide.collaboration.Annotation
import clide.collaboration.Annotations
import clide.collaboration.Plain
import clide.collaboration.AnnotationType
import isabelle._

object IsabelleMarkup {  
  val classes = Map(      
      Markup.KEYWORD1 -> "command",
      Markup.KEYWORD2 -> "keyword",
      Markup.STRING -> "string",
      Markup.ALTSTRING -> "string",
      Markup.VERBATIM -> "verbatim",
      Markup.LITERAL -> "keyword",
      Markup.DELIMITER -> "delimiter",
      Markup.TFREE -> "tfree",
      Markup.TVAR -> "tvar",
      Markup.FREE -> "free",
      Markup.SKOLEM -> "skolem",
      Markup.BOUND -> "bound",
      Markup.VAR -> "var",
      Markup.INNER_STRING -> "innerString",
      Markup.INNER_COMMENT -> "innerComment",
      Markup.DYNAMIC_FACT -> "dynamic_fact")      
      
  val classesElements = classes.keySet
  
    /* message priorities */

  private val writeln_pri = 1
  private val information_pri = 2
  private val tracing_pri = 3
  private val warning_pri = 4
  private val legacy_pri = 5
  private val error_pri = 6

  private val message_pri = Map(
    Markup.WRITELN -> writeln_pri, Markup.WRITELN_MESSAGE -> writeln_pri,
    Markup.TRACING -> tracing_pri, Markup.TRACING_MESSAGE -> tracing_pri,
    Markup.WARNING -> warning_pri, Markup.WARNING_MESSAGE -> warning_pri,
    Markup.ERROR -> error_pri, Markup.ERROR_MESSAGE -> error_pri)  
  
  def highlighting(snapshot: Document.Snapshot): Annotations = {
    val cs: List[Text.Info[Option[String]]] = snapshot.cumulate_markup(Text.Range(0,Int.MaxValue), Option.empty[String], Some(classesElements), _ =>
      {
        case (_, Text.Info(_,elem)) => Some(classes.get(elem.name))   
      })    
    cs.foldLeft(new Annotations) {
      case (as, Text.Info(range,None))    => as.plain(range.length)
      case (as, Text.Info(range,Some(c))) => as.annotate(range.length, List(AnnotationType.Class -> c))
    }    
  }
  
  def errors(snapshot: Document.Snapshot): Annotations = {
    val es: List[Text.Info[Option[String]]] = snapshot.cumulate_markup(Text.Range(0,Int.MaxValue), Option.empty[String], Some(Set(Markup.ERROR, Markup.ERROR_MESSAGE)), _ =>
      {
        case (_, Text.Info(_,elem)) =>
          Some(Some(elem.toString))
      })
    es.foldLeft(new Annotations) {
      case (as, Text.Info(range,None))    => as.plain(range.length)
      case (as, Text.Info(range,_)) => as.annotate(range.length, List(AnnotationType.Class -> "error"))      
    }
  }

  def warnings(snapshot: Document.Snapshot): Annotations = {
    val ws: List[Text.Info[Option[String]]] = snapshot.cumulate_markup(Text.Range(0,Int.MaxValue), Option.empty[String], Some(Set(Markup.WARNING, Markup.WARNING_MESSAGE)), _ =>
      {
        case (_, Text.Info(_,elem)) =>
          Some(Some(elem.toString))
      })
    ws.foldLeft(new Annotations) {      
      case (as, Text.Info(range,None))    => as.plain(range.length)
      case (as, Text.Info(range,_)) => as.annotate(range.length, List(AnnotationType.Class -> "warning"))      
    }
  }
  
  def output(snapshot: Document.Snapshot, positions: Set[Text.Offset]): Annotations = {    
    snapshot.node.commands.foldLeft (new Annotations) {
      case (as,cmd) => if (!cmd.is_ignored) {
        val state = snapshot.state.command_state(snapshot.version, cmd)
        val outputs = state.results.entries.map(_._2)
          .filterNot(Protocol.is_result(_))
          .collect{ 
            case XML.Elem(markup,body) if markup.name == Markup.WRITELN_MESSAGE =>
              AnnotationType.Output -> XML.content(body) //isabelle.Pretty.formatted(body, 120.0, isabelle.Pretty.Metric_Default).mkString("\n")
            case XML.Elem(markup,body) if markup.name == Markup.ERROR_MESSAGE =>
              AnnotationType.ErrorMessage -> XML.content(body) //isabelle.Pretty.formatted(body, 120.0, isabelle.Pretty.Metric_Default).mkString("\n")
            case XML.Elem(markup,body) if markup.name == Markup.WARNING_MESSAGE =>
              AnnotationType.WarningMessage -> XML.content(body)
          }
        as.annotate(cmd.length, outputs.toList)
      } else {
        as.plain(cmd.length)
      }
    }
  }
  
  private val tooltip_elements =
    Set(Markup.TIMING, Markup.ENTITY, Markup.SORTING, Markup.TYPING,
      Markup.ML_TYPING, Markup.PATH) 

  private def pretty_typing(kind: String, body: XML.Body): XML.Tree =
    Pretty.block(XML.Text(kind) :: Pretty.Break(1) :: body)

  def tooltip(snapshot: Document.Snapshot): Option[Text.Info[XML.Body]] =
  {
    def add(prev: Text.Info[(Timing, List[(Boolean, XML.Tree)])],
      r0: Text.Range, p: (Boolean, XML.Tree)): Text.Info[(Timing, List[(Boolean, XML.Tree)])] =
    {
      val r = snapshot.convert(r0)
      val (t, info) = prev.info
      if (prev.range == r) Text.Info(r, (t, p :: info)) else Text.Info(r, (t, List(p)))
    }

    val results =
      snapshot.cumulate_markup[Text.Info[(Timing, List[(Boolean, XML.Tree)])]](
        Text.Range(0,Int.MaxValue), Text.Info(Text.Range(0,Int.MaxValue), (Timing.zero, Nil)), Some(tooltip_elements), _ =>
        {
          case (Text.Info(r, (t1, info)), Text.Info(_, XML.Elem(Markup.Timing(t2), _))) =>
            Some(Text.Info(r, (t1 + t2, info)))
          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _))) =>
            val kind1 = space_explode('_', kind).mkString(" ")
            val txt1 = kind1 + " " + quote(name)
            val t = prev.info._1
            val txt2 =
              if (kind == Markup.COMMAND && t.elapsed.seconds >= timing_threshold)
                "\n" + t.message
              else ""
            Some(add(prev, r, (true, XML.Text(txt1 + txt2))))
          case (prev, Text.Info(r, XML.Elem(Markup.Path(name), _)))
          if Path.is_ok(name) =>
            val jedit_file = PIDE.thy_load.append(snapshot.node_name.dir, Path.explode(name))
            Some(add(prev, r, (true, XML.Text("file " + quote(jedit_file)))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            Some(add(prev, r, (true, pretty_typing("::", body))))
          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            Some(add(prev, r, (false, pretty_typing("ML:", body))))
          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _))) =>
            if (tooltips.isDefinedAt(name))
              Some(add(prev, r, (true, XML.Text(tooltips(name)))))
            else None
        }).map(_.info)

    results.map(_.info).flatMap(_._2) match {
      case Nil => None
      case tips =>
        val r = Text.Range(results.head.range.start, results.last.range.stop)
        val all_tips = (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
        Some(Text.Info(r, Library.separate(Pretty.FBreak, all_tips)))
    }
  }
  def scripts(state: String): Annotations =
    Symbol.iterator(state).foldLeft((new Annotations, false, false, false, false)){
      case ((as,sub,sup,bsub,bsup),sym) if sym.length() > 1 && Symbol.decode(sym) == Symbol.sub_decoded =>
        (as.annotate(sym.length, List(AnnotationType.Substitution -> "")),true,false,bsub,bsup)
      case ((as,sub,sup,bsub,bsup),sym) if sym.length() > 1 && Symbol.decode(sym) == Symbol.sup_decoded =>
        (as.annotate(sym.length, List(AnnotationType.Substitution -> "")),false,true,bsub,bsup)
      case ((as,sub,sup,bsub,bsup),sym) if sym.length() > 1 && Symbol.decode(sym) == Symbol.bsub_decoded =>
        (as.annotate(sym.length, List(AnnotationType.Substitution -> "")),false,false,true,bsup)
      case ((as,sub,sup,bsub,bsup),sym) if sym.length() > 1 && Symbol.decode(sym) == Symbol.bsup_decoded =>
        (as.annotate(sym.length, List(AnnotationType.Substitution -> "")),false,false,bsub,true)
      case ((as,sub,sup,bsub,bsup),sym) if sym.length() > 1 && Symbol.decode(sym) == Symbol.esub_decoded =>
        (as.annotate(sym.length, List(AnnotationType.Substitution -> "")),false,false,false,bsup)
      case ((as,sub,sup,bsub,bsup),sym) if sym.length() > 1 && Symbol.decode(sym) == Symbol.esup_decoded =>
        (as.annotate(sym.length, List(AnnotationType.Substitution -> "")),false,false,bsub,false)      
      case ((as,true,sup,bsub,bsup),sym) =>
        (as.annotate(sym.length(), List(AnnotationType.Class -> "sub")),false,false,bsub,bsup)
      case ((as,sub,true,bsub,bsup),sym) =>
        (as.annotate(sym.length(), List(AnnotationType.Class -> "sup")),false,false,bsub,bsup)
      case ((as,sub,sup,true,bsup),sym) =>
        (as.annotate(sym.length(), List(AnnotationType.Class -> "sub")),false,false,true,bsup)
      case ((as,sub,sup,bsub,true),sym) =>
        (as.annotate(sym.length(), List(AnnotationType.Class -> "sup")),false,false,bsub,true)
      case ((as,sub,sup,bsub,bsup),sym) =>
        (as.plain(sym.length),sub,sup,bsub,bsup)
    }._1
  
  def substitutions(state: String): Annotations =
    Symbol.iterator(state).foldLeft(new Annotations) {
      case (as, sym) if sym.length == 1 || Symbol.decode(sym) == sym =>
        as.plain(sym.length)
      case (as, sym) =>
        as.annotate(sym.length, List(AnnotationType.Class -> "symbol",AnnotationType.Substitution -> Symbol.decode(sym)))
    }
  
  
  def progress(state: String, snapshot: Document.Snapshot): Annotations = {
    var offset = 0
    val it = state.linesWithSeparators
    var result = new Annotations
    while (it.hasNext) {
      val line = it.next()
      overview_class(snapshot, Text.Range(offset, offset + line.length())) match {
        case None => result = result.plain(line.length())
        case Some(c) => result = result.annotate(line.length, List(AnnotationType.Progress -> c))
      }
      offset += line.length()
    }
    result
  } 
  
  private val overview_include = Protocol.command_status_markup + Markup.WARNING + Markup.ERROR    

  def overview_class(snapshot: Document.Snapshot, range: Text.Range): Option[String] =
  {
    if (snapshot.is_outdated) None
    else {
      val results =
        snapshot.cumulate_markup[(Protocol.Status, Int)](
          range, (Protocol.Status.init, 0), Some(overview_include), _ =>
          {
            case ((status, pri), Text.Info(_, elem)) =>
              if (elem.name == Markup.WARNING || elem.name == Markup.ERROR)
                Some((status, pri max message_pri(elem.name)))
              else if (overview_include(elem.name))
                Some((Protocol.command_status(status, elem.markup), pri))
              else None
          })
      if (results.isEmpty) None
      else {
        val (status, pri) =
          ((Protocol.Status.init, 0) /: results) {
            case ((s1, p1), Text.Info(_, (s2, p2))) => (s1 + s2, p1 max p2) }

        if (status.is_running) Some("running")
        else if (pri == warning_pri) Some("warning")
        else if (pri == error_pri) Some("error")
        else if (status.is_unprocessed) Some("pending")
        else if (status.is_failed) Some("failed")
        else None
      }
    }
  }
  
}
