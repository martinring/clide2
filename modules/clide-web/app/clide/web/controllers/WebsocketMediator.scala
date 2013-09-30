package clide.web.controllers

import akka.actor._
import play.api.libs.iteratee._
import clide.actors.Events._
import clide.actors.Messages._
import akka.pattern.ask
import scala.concurrent.duration._
import akka.util.Timeout
import scala.util.Success
import scala.util.Failure
import play.api.Logger

object WebsocketMediator {
  case class Init(ref: ActorRef, msg: Message)
}

class WebsocketMediator extends Actor with ActorLogging {  
  val (out,channel) = Concurrent.broadcast[Event]
  var peer = context.system.deadLetters
  var client = context.system.deadLetters
  
  def receive = {
    case WebsocketMediator.Init(ref,message) =>
      client = sender
      context.watch(client)
      ref ! message
    case EventSocket(peer,_) =>
      log.info("forwarding event socket")
      this.peer = peer
      context.watch(peer)
      client ! out
    case e: Event =>
      log.info(e.toString())
      channel.push(e)
    case msg: Message =>
      log.info(msg.toString())
      peer ! msg
    case Terminated(ref) =>
      channel.eofAndEnd()      
      context.stop(self)
  }    
}     