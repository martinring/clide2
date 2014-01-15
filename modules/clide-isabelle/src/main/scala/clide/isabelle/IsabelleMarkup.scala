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
  
  def annotations(xml: XML.Tree, c: Set[(AnnotationType.Value,String)] = Set.empty): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>
      markup.name match {
        case Markup.ERROR | Markup.BAD =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "error",
              AnnotationType.ErrorMessage -> XML.content(body))))
        case Markup.WARNING =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "warning",
              AnnotationType.WarningMessage -> XML.content(body))))        
        case Markup.INFORMATION =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "info",
              AnnotationType.InfoMessage -> XML.content(body))))
        case Markup.TYPING =>
          body2.flatMap(annotations(_,Set(              
              AnnotationType.Tooltip -> ("type: " + XML.content(body)))))
        case other =>
          body2.flatMap(annotations(_))
      }

    case XML.Elem(markup, body) =>
      val c2 = markup.name match {
        //case Markup.RUNNING | Markup.FINISHED | Markup.FAILED =>
        // Set(AnnotationType.Progress -> markup.name)
        case Markup.ENTITY =>
          val as = markup.properties.collect {
            case ("def",id) => AnnotationType.Entity -> id
            case ("ref",id) => AnnotationType.Ref -> id
          }        
          as.toSet
        case m if classes.isDefinedAt(m) => Set(AnnotationType.Class -> classes(m))
        case other                       => Set.empty
      }

      body.flatMap(annotations(_,c ++ c2))

    case XML.Text(content) => c.size match {
        case 0 => List(Plain(content.length))
        case _ => List(Annotate(content.length,c))
      }
  }

  def highlighting(header: Document.Node.Header, snapshot: Document.Snapshot): Annotations = {
    val cs: List[Text.Info[Option[String]]] = snapshot.cumulate_markup(Text.Range(0,Int.MaxValue), Option.empty[String], Some(classesElements), _ =>
      {
        case (_, Text.Info(_,elem)) => Some(classes.get(elem.name))   
      })    
    cs.foldLeft(new Annotations) {
      case (as, Text.Info(range,None))    => as.plain(range.length)
      case (as, Text.Info(range,Some(c))) => as.annotate(range.length, Set(AnnotationType.Class -> c))
    }    
  }
  
  def errors(header: Document.Node.Header, snapshot: Document.Snapshot): Annotations = {
    val es: List[Text.Info[Option[String]]] = snapshot.cumulate_markup(Text.Range(0,Int.MaxValue), Option.empty[String], Some(Set(Markup.ERROR, Markup.ERROR_MESSAGE)), _ =>
      {
        case (_, Text.Info(_,elem)) => println("err: " + elem) 
          Some(Some(elem.toString))
      })
    es.foldLeft(new Annotations) {
      case (as, Text.Info(range,None))      => as.plain(range.length)
      case (as, Text.Info(range,Some(msg))) => as.annotate(range.length, Set(AnnotationType.Class -> "error", AnnotationType.ErrorMessage -> msg))      
    }
  }
  
  def output(snapshot: Document.Snapshot, positions: Set[Text.Offset]): Annotations = {    
    snapshot.node.commands.foldLeft (new Annotations) {
      case (as,cmd) => if (!cmd.is_ignored) {
        val state = snapshot.state.command_state(snapshot.version, cmd)               
        val output = state.results.entries.map(_._2)
          .filterNot(Protocol.is_result(_))
          .collect{ case XML.Elem(markup,body) if markup.name == Markup.WRITELN_MESSAGE =>            
            isabelle.Pretty.formatted(body, 120.0, isabelle.Pretty.Metric_Default).mkString("\n") }
          .mkString("\n")
        as.annotate(cmd.length, Set(AnnotationType.Output -> output))
      } else {
        as.plain(cmd.length)
      }
    }
  }
  
  def substitutions(state: String): Annotations =
    Symbol.iterator(state).foldLeft(new Annotations) {
      case (as, sym) if sym.length == 1 || Symbol.decode(sym) == sym =>
        as.plain(sym.length)
      case (as, sym) =>
        as.annotate(sym.length, Set(AnnotationType.Class -> "symbol",AnnotationType.Substitution -> Symbol.decode(sym)))
    }
}
