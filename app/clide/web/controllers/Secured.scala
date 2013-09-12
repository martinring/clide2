package clide.web.controllers

import play.api.mvc._
import play.api.mvc.BodyParsers._
import play.api.libs.json.JsValue
import clide.models._
import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.db.slick.DB
import play.api.Play.current
import scala.concurrent.Future
import clide.actors.Infrastructure._
import clide.actors.UserServer._
import clide.actors.users.UserActor._

/**
 * Provide security features
 */
trait Secured { this: Controller with ActorAsk =>
  class AuthenticatedRequest[A](
      val user: UserInfo,
      val login: LoginInfo,
      request: Request[A])
    extends WrappedRequest[A](request)
  
  /**
   * Looks up the current user in the database and returns it.
   */  
  def sessionInfo[T](implicit request: Request[T]): Option[(String,String)] = for {
    name <- request.session.get("user")
    key  <- request.session.get("key")      
  } yield (name,key)         
 
  object Authenticated extends ActionBuilder[AuthenticatedRequest] {
    def invokeBlock[A](request: Request[A], block: AuthenticatedRequest[A] => Future[SimpleResult]) = {
      sessionInfo(request) match {
        case None => Future.successful(Results.Forbidden)
        case Some((name,key)) =>
          implicit val ec = executionContext
          (server ? WithUser(name,Validate(key))).mapTo[UserEvent].flatMap {
            case Validated(user,login) => block(new AuthenticatedRequest(user,login,request))
            case NotLoggedIn           => Future.successful(Results.Unauthorized("not-logged-in"))
            case SessionTimedOut(user) => Future.successful(Results.Unauthorized("timeout"))
            case msg                   => Future.successful(Results.InternalServerError(msg.toString))
          }
      }
    }
  }    
}