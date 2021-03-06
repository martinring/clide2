/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
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

package clide.assistants

import clide.collaboration.Annotations
import clide.models.OpenedFile
import clide.collaboration.Operation
import clide.models.ProjectInfo
import clide.models.SessionInfo
import scala.concurrent.Future

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
// should be deprecated some time in the future, when assistbehavior becomes stable
//@deprecated("Use Future-based AssistBehavior instead!","2.0-SNAPSHOT")
trait AssistantBehavior {
  /**
   * Everything that needs to be set up can be set up here. It is guaranteed, that
   * this method will be called first and no other method will be called until the
   * execution has been completed.
   *
   * @param project the project, the assistant is watching
   */
  def start(project: ProjectInfo): Unit

  /**
   * This method will be called, before the assistant will be disposed. Any resources
   * that need to be released can be released here.
   */
  def stop: Unit

  /**
   * Should return a set of mime types that the assistant will automatically
   * react on. If the set is empty, the assistant will only be activated if a user
   * actively requests it's help in a specific file or the assistant actively opens
   * a file through it's control.
   */
  def mimeTypes: Set[String]

  /**
   * called when a previously unknown file is added to the assistants scope.
   */
  def fileOpened(file: OpenedFile): Unit

  /**
   * called when a previously inactive file turns active. (i.e. sombody looks at it)
   */
  def fileActivated(file: OpenedFile): Unit

  /**
   * called when a previously active file turns inactive (i.e. everybody stopped
   * looking at the file)
   */
  def fileInactivated(file: OpenedFile): Unit

  /**
   * called when a previously open file is removed from the assistants scope.
   */
  def fileClosed(file: OpenedFile): Unit

  /**
   * called when a file in the assistants scope was edited.
   * May do long blocking comuptations. Internally it will be executed concurrently
   * while all new updates to the file will be cumulated and will appear as one update
   * after the method returned. Other Events are postponed during execution.
   *
   * @param file the state of the file **after** the edit occured.
   * @param delta the operation that has been performed
   */
  def fileChanged(file: OpenedFile, delta: Operation[Char], cursors: Seq[Cursor]): Unit

  /**
   * called when a collaborator joined the session.
   */
  def collaboratorJoined(who: SessionInfo): Unit

  /**
   * called when a collaborator left the session
   */
  def collaboratorLeft(who: SessionInfo): Unit

  /**
   * called when some active collaborator moved the cursor in some file that
   * belongs to the assistants scope.
   */
  def cursorMoved(cursor: Cursor): Unit


  /**
   * at least one client is interested in seeing the specified annotation stream
   */
  def annotationsRequested(file: OpenedFile, name: String): Unit

  /**
   * all clients dropped their interest in seeing the specified annotation stream
   */
  def annotationsDisregarded(file: OpenedFile, name: String): Unit

  /**
   * called when a chat message arrives
   * @param from username of the sender
   * @param msg the message content
   * @param tpe optional message type (TODO: Make enumeration)
   * @param timestamp
   */
  def receiveChatMessage(from: String, msg: String, tpe: Option[String], timestamp: Long): Unit
}
