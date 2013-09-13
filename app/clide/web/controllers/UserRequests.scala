package clide.web.controllers

import akka.util.Timeout
import scala.concurrent.duration._
import akka.actor.ActorRef
import play.api.Play.current
import scala.concurrent.Future
import clide.actors.Messages._
import clide.actors.Events._
import play.api.mvc._
import scala.concurrent.Future
import play.api.libs.json._
import play.api.libs.iteratee.Iteratee

trait UserRequests { this: Controller =>
  implicit val timeout = Timeout(5 seconds)
  implicit def ask(act: ActorRef) = akka.pattern.ask(act)
  implicit val executionContext = play.api.libs.concurrent.Akka.system.dispatcher
  val server = clide.actors.Infrastructure.userServer
  val Messages = clide.actors.Messages
  
  class UserAskRequest[A](val ask: (UserMessage => Future[Event]),
                          val askFor: (String => UserMessage => Future[Event]), 
                          request: Request[A])
    extends WrappedRequest[A](request)
    
  def ActorSocket(
      user: String, 
      message: UserMessage,
      deserialize: JsValue => Message,
      serialize: Event => JsValue) = WebSocket.async[JsValue] { request =>
    val auth = for {
      user <- request.session.get("user")
      key  <- request.session.get("key")      
    } yield (user,key)
    val req = auth match {
      case None => AnonymousFor(user,message)
      case Some((user,key)) => IdentifiedFor(user,key,message)
    }    
    (server ? req).mapTo[Event].map {
      case EventSocket(in,out) => 
        (Iteratee.foreach[JsValue](json => in ! deserialize(json)),
         out.map(serialize))      
    }
  }
      
  object UserRequest extends ActionBuilder[UserAskRequest] {
    def invokeBlock[A](request: Request[A], block: UserAskRequest[A] => Future[SimpleResult]) = {     
      val auth = for {
        user <- request.session.get("user")
        key  <- request.session.get("key")
      } yield (user,key)           
      val (a,aF) = auth match {
        case None       => (
            { msg: UserMessage => 
              Future.successful(NotLoggedIn) },
            { user: String => msg: UserMessage => 
              (server ? AnonymousFor(user, msg)).mapTo[Event] } )
        case Some((user,key)) => ( 
            { msg: UserMessage => 
              (server ? IdentifiedFor(user,key,msg)).mapTo[Event] },
            { user: String => msg: UserMessage => 
              (server ? IdentifiedFor(user,key,WithUser(user,msg))).mapTo[Event] })        
      }      
      block(new UserAskRequest(a,aF,request))
    }
  }
}