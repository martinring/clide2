package models.concurrency

import scala.collection.mutable.Map
import akka.actor.Actor
import akka.actor.ActorRef
import akka.actor.Props

object Server {
  val maxClients = 16
  
  def props(): Props = 
    Props(() => new Server)
  
  trait Message
  object Register extends Message
  case class Leave(id: Int) extends Message
  
  trait Reply
  object ServerFull extends Reply
  case class Registered(id: Int) extends Reply
}

class Server extends Actor {
  val doc = new Document()
  val client = new Client(0,doc)
  val clients = Map.empty[Int,ActorRef]
  def receive = {
    case Server.Register =>
      (1 to Server.maxClients)
        .find(n => !clients.isDefinedAt(n))
        .fold(sender ! Server.ServerFull) {
        case id => 
          clients += id -> sender
          sender ! Server.Registered(id)
      }
    case Server.Leave(id) =>
      clients.remove(id)
    case o: Operation => 
      if (client.applyOperation.isDefinedAt(o)) {
        client.applyOperation(o)
        clients.values.filter(_ != sender).foreach(_ ! o)
      } else
        throw new Exception ("preconditions unfulfilled")
  }
}