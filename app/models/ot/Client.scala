package models.ot

import akka.actor.{Actor,ActorRef}
import scala.reflect.ClassTag
import akka.actor.Props

class Client(server: ActorRef) extends Actor {
  var acknowledged = false
  var document: Option[Document] = None
  var revision: Option[Int] = None
  var cache: Option[Operation] = None
  
  def receive: Receive = {
    // initial state from server
    case (rev: Int, doc: Document) =>
      acknowledged = true
      revision = Some(rev)
      document = Some(doc)
      context.become(running, discardOld = true)
  }
  
  def running: Receive = {
    // concurrent operation from server
    case (rev: Int, op: Operation) =>
      revision = Some(rev)
      val newOp: Operation = cache.fold(op)(Operation.transform(_, op).get._2)
      document.map(_.apply(newOp))
      
    // local operation
    case op: Operation if acknowledged =>
      server ! op
      acknowledged = false
      
    case op: Operation =>
      cache.fold(op)(Operation.compose(_, op).get) // TODO: Error handling
      
    // acknowledgement from server
    case Acknowledgement =>
      acknowledged = true
      cache.map { op =>
        server ! op
        acknowledged = false
      }
      cache = None
  }
}

object Client {
  def props(server: ActorRef): Props = 
    Props(() => new Client(server))
}