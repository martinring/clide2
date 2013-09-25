package clide.actors.files

import clide.models._
import akka.actor._
import clide.actors.Events
import clide.actors.Messages

trait FileEventSource { this: Actor with ActorLogging =>
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