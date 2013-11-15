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

import clide.models._
import akka.actor._
import clide.actors.Events
import clide.actors.Messages

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private[actors] trait FileEventSource { this: Actor with ActorLogging =>
  import Events._
  import Messages._

  var listeners = Set[ActorRef]()

  def triggerFileEvent(event: FileEvent) {
    listeners.foreach(_ ! event)
  }

  def initFileEventSource() {
    listeners += context.parent
  }

  def receiveFileEvents: Receive = {
    case Register =>
      listeners += sender
      context.watch(sender)
    case Terminated(ref) =>
      log.warning("listener terminated before unregistering")
      listeners -= ref
    case Unregister =>
      listeners -= sender
  }
}
