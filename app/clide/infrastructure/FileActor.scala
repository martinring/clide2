package clide.infrastructure

import akka.actor.Actor
import clide.models._
import akka.actor.ActorLogging
import clide.collaboration._
import akka.actor.Props
import akka.actor.ActorRef
import scala.collection.mutable.Map
import scala.util.Success
import scala.util.Failure
import scala.concurrent.duration._
import play.api.Play
import Play.current
import akka.actor.Cancellable
import akka.actor.PoisonPill

/**
 * A FileActor is responsible for communicating with a File (i.e. reading and writing)
 * @author Martin Ring <martin.ring@dfki.de>
 */
class FileActor(project: ProjectInfo, path: String) extends Actor with ActorLogging {
  import FileActor._
  import context.dispatcher
  
  val file = Play.getFile(project.root + path)
    
  var server: Server = null
  var clients = Map[ActorRef,GenericUser]()  
  var annotations = Map[GenericUser,AnnotationStream]()
  
  var kill: Option[Cancellable] = None
  
  def nonExistent: Receive = {
    case Create =>
      log.info("create new file")
      file.createNewFile()
      server = new Server(Document(""))
      context.unbecome()
  }
  
  def receive = {
    case Register(user) =>
      log.info(f"user ${user.name} registered")
      clients += sender -> user
      sender ! SessionActor.Initialize(path, server.revision, server.text)
      kill.map(_.cancel())
      kill = None

    case Leave =>      
      clients.remove(sender) match {
        case Some(user) => log.info(f"${user.name} left")
        case None => log.error("client already left")
      }
      if (clients.isEmpty)
        kill = Some(context.system.scheduler.scheduleOnce(5 seconds)(context.self ! PoisonPill))
      
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
      
    case Save =>
      require(clients.contains(sender), "unknown sender")
      val writer = new java.io.FileWriter(file,false)
	  writer.write(server.text)
	  writer.flush()
	  writer.close()
	  
    case Delete =>
      require(clients.contains(sender), "unknown sender")
      file.delete()
      context.become(nonExistent)
  }    
  
  override def preStart() {
    import context.dispatcher
    log.info("file actor starting")
    if (!file.exists()) {
      context.become(nonExistent)
      server = new Server(Document("#FILE DOES NOT EXIST!#"))
    } else {
      val content = scala.io.Source.fromFile(file)
      server = new Server(Document(content.mkString))
      content.close()
    }
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
  case object Save extends Request
  case object Delete extends Request
  case object Create extends Request
}