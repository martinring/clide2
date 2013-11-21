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

//package clide.isabelle
//
//import akka.actor.ActorRef
//import akka.actor.actorRef2Scala
//import clide.assistants.DocumentModel
//import clide.collaboration.Annotations
//import clide.collaboration.Delete
//import clide.collaboration.Insert
//import clide.collaboration.Operation
//import clide.collaboration.Retain
//import clide.models.ProjectInfo
//import isabelle.Document
//import isabelle.Exn
//import isabelle.Session
//import isabelle.Text
//import isabelle.Thy_Header
//import isabelle.Command
//import isabelle.Protocol
//import isabelle.XML
//
//class IsabelleDocumentModel(server: ActorRef, project: ProjectInfo, session: Session) extends DocumentModel(server, project) {
//  def nodeName = {
//    val name = file.path.mkString("/")
//    Thy_Header.thy_name(name).map { theory =>
//      Document.Node.Name(name, project.root, theory)
//    }
//  }.get
//
//  def nodeHeader =
//    Exn.capture {
//      session.thy_load.check_thy_text(nodeName, state)
//    } match {
//      case Exn.Res(header) => header
//      case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
//    }
//
//  var overlays = Document.Node.Overlays.empty
//
//  def insertOverlay(command: isabelle.Command, fn: String, args: List[String]) = {
//    overlays = overlays.insert(command, fn, args)
//  }
//
//  def removeOverlay(command: isabelle.Command, fn: String, args: List[String]) = {
//    overlays = overlays.remove(command, fn, args)
//  }
//
//  def perspective: Document.Node.Perspective_Text = {
//    Document.Node.Perspective(true, Text.Perspective.full, overlays)
//  }
//
//  def initEdits: List[(Document.Node.Name,Document.Node.Edit[Text.Edit,Text.Perspective])] = {
//    val name = nodeName
//    List(session.header_edit(name, nodeHeader),
//         name -> Document.Node.Clear(),
//         name -> Document.Node.Edits(List(Text.Edit.insert(0,state))),
//         name -> perspective)
//  }
//
//  def opToEdits(operation: Operation): List[Text.Edit] = operation.actions.foldLeft((0,Nil: List[Text.Edit])) {
//    case ((i,edits),Retain(n)) => (i+n,edits)
//    case ((i,edits),Delete(n)) => (i+n,Text.Edit.remove(i,Seq.fill(n)('-').mkString) :: edits)
//    case ((i,edits),Insert(s)) => (i+s.length,Text.Edit.insert(i,s) :: edits)
//  }._2.reverse // TODO: Do we need to reverse???
//
//  def opToDocumentEdits(operation: Operation): List[Document.Edit_Text] = {
//    val name = nodeName
//    val edits = opToEdits(operation)
//    List(session.header_edit(name, nodeHeader),
//      name -> Document.Node.Edits(edits),
//      name -> perspective)
//  }
//
//  def annotate: List[(String,Annotations)] = {
//    List("highlighting"  -> IsabelleMarkup.highlighting(nodeHeader,snapshot),
//         "substitutions" -> IsabelleMarkup.substitutions(state),
//         "output"        -> IsabelleMarkup.output(snapshot))
//  }
//
//  def commandAt(pos: Int): Option[Command] = {
//    val node = snapshot.version.nodes(nodeName)
//    val commands = snapshot.node.command_range(pos)
//    if (commands.hasNext) {
//      val (cmd0,_) = commands.next
//      node.commands.reverse.iterator(cmd0).find(cmd => !cmd.is_ignored)
//    } else None
//  }
//
//  override def getInfo(pos: Int): Option[String] = commandAt(pos).map { cmd =>
//    val state = snapshot.state.command_state(snapshot.version, cmd)
//    state.results.entries.map(_._2)
//         .filterNot(Protocol.is_result(_))
//         .map(XML.content(_))
//         .mkString("\n")
//  }
//
//  def changed(op: Operation) {
//    val edits = opToDocumentEdits(op)
//    session.update(edits)
//  }
//
//  var snapshot: Document.Snapshot = null
//
//  def initialize() {
//    session.update(initEdits)
//    session.commands_changed += { change =>
//      snapshot = session.snapshot(nodeName, Nil)
//      if (snapshot.state.tip_stable && (change.nodes.contains(nodeName) &&
//          change.commands.exists(snapshot.node.commands.contains)))
//        triggerRefresh
//    }
//  }
//}
