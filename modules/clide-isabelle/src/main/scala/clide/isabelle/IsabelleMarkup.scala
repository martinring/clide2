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
import isabelle.Document
import isabelle.Markup
import isabelle.Symbol
import isabelle.XML
import isabelle.HTML
import clide.collaboration.AnnotationType
import isabelle.Protocol
import isabelle.Text

object IsabelleMarkup {  
  val classes = Map(      
      Markup.KEYWORD1 -> "keyword",
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
              AnnotationType.WarningMessage -> isabelle.Pretty.formatted(body, 120.0, isabelle.Pretty.Metric_Default).mkString("\n")                       
          }
        as.annotate(cmd.length, outputs.toList)
      } else {
        as.plain(cmd.length)
      }
    }
  }
  
  def typeInfo(snapshot: Document.Snapshot): Annotations = {
    val ws: List[Text.Info[Option[String]]] = snapshot.cumulate_markup(Text.Range(0,Int.MaxValue), Option.empty[String], Some(Set(Markup.TYPING)), _ =>
      {
        case (_, Text.Info(_,elem)) =>
          Some(Some(elem.toString))
      })
    ws.foldLeft(new Annotations) {
      case (as, Text.Info(range,None))      => as.plain(range.length)
      case (as, Text.Info(range,Some(msg))) => as.annotate(range.length, List(AnnotationType.Tooltip -> msg))      
    }
  }    
  
  def substitutions(state: String): Annotations =
    Symbol.iterator(state).foldLeft(new Annotations) {
      case (as, sym) if sym.length == 1 || Symbol.decode(sym) == sym =>
        as.plain(sym.length)
      case (as, sym) =>
        as.annotate(sym.length, List(AnnotationType.Class -> "symbol",AnnotationType.Substitution -> Symbol.decode(sym)))
    }
}
