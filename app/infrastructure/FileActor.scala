package infrastructure

import akka.actor.Actor
import models.GenericUser
import models.ProjectInfo
import akka.actor.ActorLogging
import models.collab.Document
import models.collab.Server
import akka.actor.Props
import akka.actor.ActorRef
import scala.collection.mutable.Map
import models.collab.Operation
import scala.util.Success
import scala.util.Failure
import models.collab.AnnotationStream
import scala.concurrent.duration._

/**
 * A FileActor is responsible for communicating with a File (i.e. reading and writing)
 * @author Martin Ring <martin.ring@dfki.de>
 */
class FileActor(project: ProjectInfo, path: String) extends Actor with ActorLogging {
  import FileActor._
  
  var server  = new Server(Document(""))
  var clients = Map[ActorRef,GenericUser]()  
  var annotations = Map[GenericUser,AnnotationStream]()
  
  def receive = {
    case Register(user) =>
      log.info(f"user ${user.name} registered")
      clients += sender -> user
      sender ! SessionActor.Initialize(path, server.revision, server.text)
      
    case Leave =>
      clients.remove(sender) match {
        case Some(user) => log.info(f"${user.name} left")
        case None => log.error("client already left")
      }
      
    case Edit(rev, operation) =>
      require(clients.contains(sender), "unknown sender")
      server.applyOperation(rev, operation) match {
        case Success(op) =>
          clients.keys.filter(_ != sender).foreach(_ ! SessionActor.Edited(path, op))
          sender ! SessionActor.Acknowledgement(path)
        case Failure(e) =>
          throw e
      }
      
    case Annotate(rev,as) =>
      require(clients.contains(sender), "unknown sender")
      server.transformAnnotation(rev, as) match {
        case Success(as) =>
          clients.keys.filter(_ != sender).foreach(_ ! SessionActor.Annotated(path, as))
          sender ! SessionActor.Acknowledgement(path)
        case Failure(e) =>
          throw e
      }
  }    
  
  override def preStart() {    
    import context.dispatcher
    log.info("file actor starting")    
  }
  
  override def postStop() {
    log.info("file actor stopped")
  }
}

object FileActor {
  trait Request
  case class Register(user: GenericUser) extends Request
  case object Leave extends Request
  case class Edit(revision: Int, operation: Operation) extends Request
  case class Annotate(revision: Int, annotations: AnnotationStream) extends Request
}