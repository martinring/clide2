 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 **                                                                           **
 **  This file is part of Clide.                                              **
 **                                                                           **
 **  Clide is free software: you can redistribute it and/or modify            **
 **  it under the terms of the GNU General Public License as published by     **
 **  the Free Software Foundation, either version 3 of the License, or        **
 **  (at your option) any later version.                                      **
 **                                                                           **
 **  Clide is distributed in the hope that it will be useful,                 **
 **  but WITHOUT ANY WARRANTY; without even the implied warranty of           **
 **  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
 **  GNU General Public License for more details.                             **
 **                                                                           **
 **  You should have received a copy of the GNU General Public License        **
 **  along with Clide.  If not, see <http://www.gnu.org/licenses/>.           **
 \*                                                                           */

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

object IsabelleMarkup {
  def annotations(xml: XML.Tree, c: Set[(AnnotationType.Value,String)] = Set.empty): List[Annotation] = xml match {
    case XML.Wrapped_Elem(markup, body, body2) =>
      println("marlup:" + markup)
      println("bory: " + body)
      println("body2: " + body2)

      markup.name match {
        case Markup.ERROR | Markup.BAD =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "error")))
        case Markup.WARNING =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "warning")))
        case Markup.WRITELN =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "info")))
        case Markup.INFORMATION =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class -> "info")))
        case Markup.TYPING =>
          body2.flatMap(annotations(_,Set(
              AnnotationType.Class   -> "typing")))
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

  /**
   *  TODO
  def tooltips(snapshot: Document.Snapshot): Annotations = {

  }*/

  def highlighting(header: Document.Node.Header, snapshot: Document.Snapshot): Annotations = {
    val xml = snapshot.state.markup_to_XML(snapshot.version, snapshot.node, _ => true)
    xml.flatMap(annotations(_)).foldLeft(new Annotations) {
      case (as, Plain(n))      => as.plain(n)
      case (as, Annotate(n,c)) => as.annotate(n, c)
    }
  }

  def output(snapshot: Document.Snapshot): Annotations = {
    val node = snapshot.version.nodes(snapshot.node_name)
    node.commands.foldLeft (new Annotations) {
      case (as,cmd) => if (!cmd.is_ignored) {
        val state = snapshot.state.command_state(snapshot.version, cmd)
        val output = state.results.entries.map(_._2)
          .filterNot(Protocol.is_result(_))
          .map(XML.content(_))
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
