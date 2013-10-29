 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.actors.files

import clide.models._
import akka.actor._
import clide.actors.Events
import clide.actors.Messages

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private trait FileEventSource { this: Actor with ActorLogging =>
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