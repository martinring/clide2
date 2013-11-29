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

import com.typesafe.config.ConfigFactory
import akka.actor.ActorSystem
import akka.actor.Props
import akka.kernel.Bootable
import isabelle.Isabelle_System
import scala.concurrent.duration._
import clide.assistants.AssistBehavior
import clide.assistants.AssistantControl
import clide.assistants.AssistantServer
import clide.models.ProjectInfo
import scala.concurrent.Future
import clide.models.OpenedFile
import scala.collection.mutable.Map
import clide.collaboration.Operation
import clide.models.SessionInfo
import isabelle.Build
import isabelle.Session
import scala.concurrent.Promise
import scala.concurrent.Await
import isabelle.XML
import isabelle.Path
import isabelle.Document
import clide.assistants.Cursor
import akka.actor.Cancellable

object Isabelle extends AssistantServer(IsabelleAssistBehavior) {
  override def startup() {
    Isabelle_System.init()
    super.startup()
  }

  override def shutdown() {
    scala.actors.Scheduler.shutdown()
    super.shutdown()
  }
}

trait Control {
  def control: AssistantControl
}

case class IsabelleAssistBehavior(control: AssistantControl) extends AssistBehavior with Control
  with IsabelleSession with IsabelleConversions {
  
  def mimeTypes = Set("text/x-isabelle")
  
  val thys = scala.collection.mutable.Map.empty[Document.Node.Name,(Document.Version,OpenedFile)]
  
  def fileOpened(file: OpenedFile) = {
    control.log.info("fileOpened({})", file.info.path)
    session.update(initEdits(file,Seq.empty))
    nextChange
  }
  def fileActivated(file: OpenedFile) = {
    control.log.info("fileActivated({})", file.info.path)
    session.update(initEdits(file,Seq.empty))
    nextChange
  } 
  def fileInactivated(file: OpenedFile) = {
    session.update(closeEdits(file))
    nextChange
  }
  
  def fileClosed(file: OpenedFile) = {
    session.update(removeEdits(file))
    nextChange
  }
  
  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]) = {
    control.log.info("fileChanged({},{},...)", file.info.path, delta)
    val edits = opToDocumentEdits(file, cursors, delta)
    session.update(edits)
    nextChange
  }

  def collaboratorJoined(who: SessionInfo) = Future.successful(())
  def collaboratorLeft(who: SessionInfo) = Future.successful(())
  
  def cursorMoved(cursor: Cursor) = Future.successful(())
  def receiveChatMessage(from: String, msg: String, tpe: Option[String], timestamp: Long) = Future.successful(())
}

object IsabelleApp extends App {
  Isabelle.startup()
  readLine()
  scala.actors.Scheduler.shutdown()
  Isabelle.shutdown()
  Isabelle.system.awaitTermination()
  sys.exit()
}