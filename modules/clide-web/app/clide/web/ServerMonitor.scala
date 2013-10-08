package clide.web

import akka.actor._
import scala.concurrent.duration._

object ServerMonitor {
  case object Request
  case class Reply(ref: ActorRef)
}

class ServerMonitor(path: String) extends Actor with ActorLogging {
  import ServerMonitor._
  
  var server: Option[ActorRef] = None  
  var listeners: Set[ActorRef] = Set.empty
  
  def identifyServer() =
    context.actorSelection(path) ! Identify("server")
  
  def receive = {
    case ActorIdentity("server", Some(ref)) =>
      server = Some(ref)
      context.watch(ref)
      listeners.foreach(_ ! Reply(ref))
      listeners = Set.empty
      log.info(s"connected to the server at $path")
      
    case ActorIdentity("server", None) =>
      log.warning(s"couldnt reach the server at $path")
      server = None      
      import context.dispatcher
      context.system.scheduler.scheduleOnce(1 second)(identifyServer())      
      
    case Terminated(ref) if Some(ref) == server =>
      log.warning("server terminated")
      server = None
      identifyServer()
    
    case Request =>
      server.fold(listeners += sender)(sender ! Reply(_))
  }
  
  override def preStart() {
    identifyServer()
  }
}
