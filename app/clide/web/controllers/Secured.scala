package clide.web.controllers

import play.api.mvc._
import play.api.mvc.BodyParsers._
import play.api.libs.json.JsValue
import clide.models.{Users,User}
import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.db.slick.DB
import play.api.Play.current
import scala.concurrent.Future

/**
 * Provide security features
 */
trait Secured { this: Controller =>
  sealed trait RefuseReason
  case object TimedOut extends RefuseReason
  case object NoSession extends RefuseReason
  
  class AuthenticatedRequest[A](val user: User, request: Request[A])
    extends WrappedRequest[A](request)
  
  /**
   * Looks up the current user in the database and returns it.
   */  
  def getSessionUser[T](implicit request: Request[T]): Either[RefuseReason,User] =
    request.session.get("session").toRight(NoSession).right.flatMap { session => 
      DB.withSession { implicit s => Users.getBySession(session).firstOption.toRight(TimedOut) }
    }
 
  object Authenticated extends ActionBuilder[AuthenticatedRequest] {
    def invokeBlock[A](request: Request[A], block: AuthenticatedRequest[A] => Future[SimpleResult]) = {
      getSessionUser(request) match {
        case Left(TimedOut)  => Future.successful(Results.Unauthorized)
        case Left(NoSession) => Future.successful(Results.Forbidden)
        case Right(user)     => block(new AuthenticatedRequest(user,request))
      }
    }
  }
}