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