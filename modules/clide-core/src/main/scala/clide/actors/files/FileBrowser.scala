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
package clide.actors.files

import akka.actor._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models.ProjectAccessLevel

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private[actors] object FileBrowser {
  def apply(write: Boolean, target: ActorRef) =
    Props(classOf[FileBrowser], write, target)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private[actors] class FileBrowser(write: Boolean, var target: ActorRef) extends Actor with ActorLogging {
  var peer: ActorRef = context.system.deadLetters

  def receive = {
    case StartFileBrowser =>
      peer = sender
      target ! Register
      context.watch(target)
      context.watch(peer)
      peer ! EventSocket(self,"files")
    case m: FileMessage =>
      log.info(m.toString)
      target ! m
    case e: FileEvent =>
      log.info(e.toString)
      peer ! e
    case Terminated(ref) if ref == peer =>
      context.stop(self)
      target ! Unregister
    case Terminated(ref) if ref == target =>
      context.stop(self)
      peer ! UnexpectedTermination
  }
}
