package infrastructure

import akka.actor.Actor
import models._
import akka.actor.ActorLogging
import akka.actor.PoisonPill
import akka.actor.Scheduler
import play.api.Play.current
import scala.concurrent.duration._
import java.io.File
import akka.pattern.ask
import scala.util.Failure
import scala.util.Success
import play.api.libs.concurrent.Akka
import akka.util.Timeout
import scala.concurrent.ExecutionContext
import scala.concurrent.Await
import akka.actor.ActorRef
import scala.collection.mutable.Buffer
import models.collab._

/**
 * The SessionActor coordinates a client session and provides the 
 * communication interface between the server system and a 
 * generic client.
 * @author Martin Ring <martin.ring@dfki.de>
 */
class SessionActor(user: GenericUser, project: Project) extends Actor with ActorLogging {
  import context.dispatcher  
  import SessionActor._
  
  implicit val timeout = Timeout(1 second)
    
  def receive = {
    case CloseSession =>
      context.stop(self)
    case OpenFile(path: String) =>
      // TODO: Check Rights      
      context.parent.forward(ProjectActor.WithFile(path,FileActor.Register(user)))
    case EditFile(path, revision, operation) =>
      // TODO: Check Rights
      context.parent.forward(ProjectActor.WithFile(path,FileActor.Edit(revision, operation)))
    case whatever => println(whatever)
  }
  
  override def preStart() {
    log.info(f"session started for ${user.name}")
  }
  
  override def postStop() {
    log.info(f"session closed (${user.name})")
  }
}

object SessionActor {
  trait Request
  case object CloseSession extends Request
  case class OpenFile(path: String) extends Request
  case class EditFile(path: String, revision: Int, operation: Operation) extends Request
  
  trait Reply
  case class Initialize(path: String, revision: Int, content: String) extends Reply
  case class Edited(path: String, operation: Operation) extends Reply
  case class Acknowledgement(path: String) extends Reply  
  
  import play.api.libs.json._
  import play.api.libs.functional.syntax._
  
  object Request {
    implicit object reads extends Reads[Request] {
      def reads(json: JsValue): JsResult[Request] = (json \ "type").asOpt[String] match {
        case Some("register") =>
          (json \ "path").validate[String].map(OpenFile)
        case Some("change") => for {
          path <- (json \ "path").validate[String]
          rev  <- (json \ "rev").validate[Int]
          op   <- (json \ "op").validate[Operation]
        } yield EditFile(path, rev, op)
        case _ => JsError("could not translate message")
      } 
    }
  }
  
  object Reply {
    implicit object writes extends Writes[Reply] {
      def writes(reply: Reply): JsValue = reply match {
        case Initialize(path, rev, s) => Json.obj (
          "type" -> "init",
          "path" -> path,
          "rev"  -> rev,
          "text" -> s
        )
        case _ => JsString("could not translate message")
      }
    }
  }  
}