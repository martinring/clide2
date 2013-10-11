package clide.actors.util

import akka.actor._
import scala.concurrent.duration._

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