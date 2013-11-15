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

package clide.assistants

import scala.concurrent.Future
import clide.models.OpenedFile
import clide.collaboration.Annotations
import clide.collaboration.Operation
import akka.event.LoggingAdapter
import akka.actor.Actor

/**
 * Defines the controls, which an AssistantBehavior is capable of. Every method is non-blocking
 * i.e. asynchronous.
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
trait AssistantControl {
  val log: LoggingAdapter

  def chat(message: String, tpe: Option[String] = None): Unit

  /**
   * Requests to open a file at the specified path. Will fulfill the future once the
   * file is available. Creates the file if it doesn't exist already.
   *
   * @param path relative (wrt the project) path to the file
   */
  def openFile(path: Seq[String]): Future[OpenedFile]

  /**
   * Annotate a file
   *
   * @param file the state of the file, which is being referenced
   * @param name the name of the annotation stream to update
   * @param annotations the updated annotation stream
   */
  def annotate(file: OpenedFile, name: String, annotations: Annotations): Unit

  /**
   * Change a file
   *
   * @param file the state of the file, which is being referenced
   * @param edit the operation which is applied to the file state
   * @returns a future indicating the acknowledgement from the server
   */
  def edit(file: OpenedFile, edit: Operation): Future[Unit]

  /**
   * Stops the assistant
   */
  def stop(): Unit
}
