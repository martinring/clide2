package infrastructure

import akka.actor.Actor
import models.GenericUser
import models.Project
import akka.actor.ActorLogging
import models.collab.Document
import models.collab.Server
import akka.actor.Props
import akka.actor.ActorRef
import scala.collection.mutable.Buffer
import models.collab.Operation
import scala.util.Success
import scala.util.Failure

/**
 * A FileActor is responsible for communicating with a File (i.e. reading and writing)
 * @author Martin Ring <martin.ring@dfki.de>
 */
class FileActor(project: Project, path: String) extends Actor with ActorLogging {
  import FileActor._
  
  var server  = new Server(Document(""))
  var clients = Buffer[ActorRef]()
  
  def receive = {
    case Register(user) =>
      log.info(f"user ${user.name} registered")
      clients += sender
      sender ! SessionActor.Initialize(path, server.revision, server.text)
    case Edit(rev, operation) =>
      require(clients.contains(sender), "unknown sender")
      server.applyOperation(rev, operation) match {
        case Success(op) =>
          clients.filter(_ != sender).foreach(_ ! SessionActor.Edited(path, op))
          sender ! SessionActor.Acknowledgement(path)
        case Failure(e) =>
          throw e
      }
  }    
  
  override def preStart() {    
    log.info("file actor starting")
  }
  
  override def postStop() {
    log.info("file actor stopped")
  }
}

object FileActor {
  trait Request
  case class Register(user: GenericUser) extends Request
  case class Edit(revision: Int, operation: Operation) extends Request
}