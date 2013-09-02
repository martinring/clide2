package infrastructure

import akka.actor.ActorRef
import models._
import models.collab._


object Messages {
  sealed trait Message

  sealed trait Request extends Message
  case class   OpenSession(user: User,project: Project)
  case object  CloseSession
  case class   OpenFile(path: String)
  case class   EditFile(path: String, operation: Operation)
  case class   CloseFile(path: String)  
  
  sealed trait Reply extends Message
  case class   Welcome(session: ActorRef)
  case class   Error(message: String)
  case class   EditAcknowledged(path: String)
  case class   FileEdited(path: String, operation: Operation, user: String)  

  import play.api.libs.json._
  
  object Request {
    implicit object reads extends Reads[Request] {
      def reads(json: JsValue): JsResult[Request] = json match {
        case _ => JsError("could not translate message")
      }
    }
  }
  
  object Reply {
    implicit object writes extends Writes[Reply] {
      def writes(reply: Reply): JsValue = reply match {
        case _ => JsString("could not translate message")
      }
    }
  }
}