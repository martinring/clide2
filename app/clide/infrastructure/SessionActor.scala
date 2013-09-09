package clide.infrastructure

import akka.actor.Actor
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
import clide.collaboration._
import clide.models._
import akka.actor.Props

/**
 * The SessionActor coordinates a client session and provides the 
 * communication interface between the server system and a 
 * generic client.
 * @author Martin Ring <martin.ring@dfki.de>
 */
class SessionActor(user: GenericUser, project: ProjectInfo) extends Actor with ActorLogging {
  import context.dispatcher  
  import SessionActor._
  
  private var peer: Option[ActorRef] = None 
  
  implicit val timeout = Timeout(1 second)
  
  val annotator = context.actorOf(Props(new HelloAnnotator(context.self)),"annotator")
    
  def receive = {
    case Register =>
      peer = Some(sender)
      context.become(active)
      sender ! ServerActor.WelcomeToSession(self)
  }
  
  def active: Receive = {
    case Register =>
      sender ! ServerActor.SessionAlreadyInUse
    case Leave =>
      peer = None
      context.unbecome()
    case OpenFile(path: String) =>
      // TODO: Check Rights
      if (sender != annotator)
        annotator ! HelloAnnotator.ListenTo(path)
      context.parent.forward(ProjectActor.WithFile(path,FileActor.Register(user)))
    case CloseFile(path: String) =>
      context.parent.forward(ProjectActor.WithFile(path,FileActor.Leave))
    case EditFile(path, revision, operation) =>
      // TODO: Check Rights
      context.parent.forward(ProjectActor.WithFile(path,FileActor.Edit(revision, operation)))
    case AnnotateFile(path, rev, ann) =>
      // TODO: Check Rights
      context.parent.forward(ProjectActor.WithFile(path,FileActor.Annotate(rev,ann)))
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
  case object Register extends Request
  case object Leave    extends Request
  case class OpenFile(path: String) extends Request
  case class CloseFile(path: String) extends Request
  case class EditFile(path: String, revision: Int, operation: Operation) extends Request
  case class AnnotateFile(path: String, revision: Int, annotation: AnnotationStream) extends Request
  
  trait Reply
  case class Initialize(path: String, revision: Int, content: String) extends Reply
  case class Edited(path: String, operation: Operation) extends Reply
  case class Annotated(path: String, before: AnnotationStream, after: AnnotationStream) extends Reply
  case class Acknowledgement(path: String) extends Reply  
  
  import play.api.libs.json._
  import play.api.libs.functional.syntax._
  
  object Request {
    implicit object reads extends Reads[Request] {
      def reads(json: JsValue): JsResult[Request] = (json \ "type").asOpt[String] match {
        case Some("register") =>
          (json \ "path").validate[String].map(OpenFile)
        case Some("leave") =>
          (json \ "path").validate[String].map(CloseFile)
        case Some("change") => for {
          path <- (json \ "path").validate[String]
          rev  <- (json \ "rev").validate[Int]
          op   <- (json \ "op").validate[Operation]
        } yield EditFile(path, rev, op)
        case _ => JsError("could not translate request")
      } 
    }
  }
  
  private def diff(a: JsValue, b: JsValue): JsValue = {
    import org.json4s.native.JsonMethods._
    val ja = parse(a.toString)
    val jb = parse(b.toString)
    ja.diff(jb) match {      
      case org.json4s.Diff(changed, added, deleted) =>
        if (changed != org.json4s.JNothing)
          println("changed: " + compact(render(changed)))
        if (added != org.json4s.JNothing)
          println("added: " + pretty(render(added)))
        if (deleted != org.json4s.JNothing)
          println("deleted: " + pretty(render(deleted)))
        b
    }
  }
  
  object Reply {
    implicit object writes extends Writes[Reply] {
      def writes(reply: Reply): JsValue = reply match {
        case Initialize(path, rev, s) => Json.obj (
          "type" -> "init",
          "path" -> path,
          "rev"  -> rev,
          "text" -> s)
        case Acknowledgement(path) => Json.obj(
          "type" -> "ack",
          "path" -> path)
        case Edited(path, operation) => Json.obj (
          "type" -> "edit",
          "path" -> path,
          "op"   -> operation)
        case Annotated(path, before, after) => Json.obj (
          "type" -> "ann",
          "path" -> path,
          "as"   -> diff(Json.toJson(before),Json.toJson(after)))
        case _ => JsString("could not translate reply")
      }
    }
  }  
}