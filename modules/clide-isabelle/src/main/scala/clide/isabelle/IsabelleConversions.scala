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

import isabelle._
import clide.models.OpenedFile
import clide.assistants.Cursor
import clide.collaboration.{Operation,Retain,Insert,Delete}

trait IsabelleConversions { self: IsabelleSession =>
  implicit def fileToNodeName(file: OpenedFile): Document.Node.Name = {
    val name = file.info.path.mkString("/")
    Thy_Header.thy_name(name).map { theory =>
      Document.Node.Name(name, project.root, theory)
    }
  }.get

  implicit def fileToNodeHeader(file: OpenedFile): Document.Node.Header =
    Exn.capture {
      session.thy_load.check_thy_text(file, file.state)
    } match {
      case Exn.Res(header) => header
      case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
    }

  val overlays = Document.Node.Overlays.empty

  implicit def cursorsToPerspective(cursors: Seq[Cursor]): Document.Node.Perspective_Text = {
    // TODO: User cursors to determine perspective or transmit perspective explicitly from clients
    Document.Node.Perspective(true, Text.Perspective.full, overlays)
  }

  def initEdits(file: OpenedFile, cursors: Seq[Cursor]): List[(Document.Node.Name,Document.Node.Edit[Text.Edit,Text.Perspective])] = {
    val name: Document.Node.Name = file
    List(session.header_edit(name,file),
         name -> Document.Node.Clear(),
         name -> Document.Node.Edits(List(Text.Edit.insert(0,file.state))),
         name -> cursors)
  }

  def opToEdits(operation: Operation): List[Text.Edit] = operation.actions.foldLeft((0,Nil: List[Text.Edit])) {
    case ((i,edits),Retain(n)) => (i+n,edits)
    case ((i,edits),Delete(n)) => (i+n,Text.Edit.remove(i,Seq.fill(n)('-').mkString) :: edits)
    case ((i,edits),Insert(s)) => (i+s.length,Text.Edit.insert(i,s) :: edits)
  }._2.reverse // TODO: Do we need to reverse???

  def opToDocumentEdits(file: OpenedFile, cursors: Seq[Cursor], operation: Operation): List[Document.Edit_Text] = {
    val name: Document.Node.Name = file
    val edits = opToEdits(operation)
    List(session.header_edit(name, file),
      name -> Document.Node.Edits(edits),
      name -> cursors)
  }

  def commandAt(file: OpenedFile, snapshot: Document.Snapshot, pos: Int): Option[Command] = {
    val node = snapshot.version.nodes(file)
    val commands = snapshot.node.command_range(pos)
    if (commands.hasNext) {
      val (cmd0,_) = commands.next
      node.commands.reverse.iterator(cmd0).find(cmd => !cmd.is_ignored)
    } else None
  }
}
