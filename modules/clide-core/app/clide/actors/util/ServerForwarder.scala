 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.actors.util

import akka.actor._
import scala.concurrent.duration._

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ServerForwarder(path: String) extends Actor with Stash with ActorLogging {
  def receive = connecting
  
  def connect() {
    log.info("connecting to server at {}", path)
    context.actorSelection(path) ! Identify("server")
  }
  
  def connecting: Receive = {
    connect()
    context.setReceiveTimeout(4 seconds)
    
    {
      case ActorIdentity("server",Some(ref)) =>       
        context.become(connected(ref))
      case ActorIdentity("server",None) =>
      case ReceiveTimeout => connect()
      case _ => stash()
    }
  }
  
  def connected(server: ActorRef): Receive = {
    log.info("connected")
    context.watch(server)   
    context.setReceiveTimeout(Duration.Undefined)
    unstashAll()
    
    {
      case Terminated(`server`) =>
        context.become(connecting)
      case ActorIdentity("server",_) =>
      case msg =>
        server forward msg
    }
  }
}