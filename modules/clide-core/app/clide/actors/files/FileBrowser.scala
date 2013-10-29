 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.actors.files

import akka.actor._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models.ProjectAccessLevel

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object FileBrowser {
  def props(write: Boolean, target: ActorRef) = 
    Props(classOf[FileBrowser], write, target)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class FileBrowser(write: Boolean, var target: ActorRef) extends Actor with ActorLogging {
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