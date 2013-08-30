package controllers

import play.api.mvc._
import play.api.mvc.BodyParsers._
import play.api.libs.json.JsValue
import models.{Users,User}
import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.db.slick.DB
import play.api.Play.current

/**
 * Provide security features
 */
trait Secured { this: Controller =>
  sealed trait RefuseReason
  case object TimedOut extends RefuseReason
  case object NoSession extends RefuseReason
  
  /**
   * Looks up the current user in the database and returns it.
   */  
  def getSessionUser[T](implicit request: Request[T]): Either[RefuseReason,User] =
    request.session.get("session").toRight(NoSession).right.flatMap { session => 
      DB.withSession { implicit s => Users.getBySession(session).firstOption.toRight(TimedOut) }
    }
  
  /** 
   * Action for authenticated users.
   */
  def Authenticated[T](parser: BodyParser[T])(f: => User => Request[T] => Result) = Action(parser) { implicit request =>
    getSessionUser match {
      case Left(TimedOut) =>  Results.Unauthorized
      case Left(NoSession) => Results.Forbidden
      case Right(user) => f(user)(request)
    }
  }
  
  def Authenticated(f: => User => Request[AnyContent] => Result): Action[AnyContent] = 
    Authenticated(parse.anyContent)(f)       
}