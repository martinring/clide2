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

package clide.haskell

import java.io.FileWriter

import scala.Array.canBuildFrom
import scala.collection.mutable.Map
import scala.sys.process.stringSeqToProcess

import clide.assistants._
import clide.collaboration._
import clide.models._

object Scala extends AssistantServer(ScalaBehavior)

case class ScalaBehavior(control: AssistantControl) extends AssistBehavior {
  val mimeTypes = Set("text/x-scala")

  val log = control.log
  
  var project: ProjectInfo = null

  def start(project: ProjectInfo) = {
    this.project = project
    noop
  }

  def stop = noop

  def fileOpened(file: OpenedFile) = noop

  def fileActivated(file: OpenedFile) = noop

  def fileInactivated(file: OpenedFile) = noop

  def fileClosed(file: OpenedFile) = noop

  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]) = noop

  def collaboratorJoined(who: SessionInfo) = noop

  def collaboratorLeft(who: SessionInfo) = noop

  def cursorMoved(cursor: Cursor) = noop
   
  def annotationsRequested(file: OpenedFile, name: String) = noop
  
  def annotationsDisregarded(file: OpenedFile, name: String) = noop
  
  def receiveChatMessage(from: SessionInfo, msg: String, tpe: Option[String], timestamp: Long) = noop
}

object ScalaApp extends App {
  Scala.startup()
  readLine()
  Scala.shutdown()
}
