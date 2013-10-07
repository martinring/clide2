package clide.actors.files

import akka.actor._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models.ProjectAccessLevel

class FileBrowser(write: Boolean, var target: ActorRef) extends Actor with ActorLogging {
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