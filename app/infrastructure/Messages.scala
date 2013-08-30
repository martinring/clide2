package infrastructure

import akka.actor.ActorRef
import models._


object Messages {
  sealed trait Message

  sealed trait Request extends Message
  case class OpenSession(user: User,project: Project)
	
  sealed trait Reply extends Message
  case class Welcome(session: ActorRef)

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