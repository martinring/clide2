package controllers

import play.api.mvc._
import play.api.mvc.BodyParsers._
import play.api.libs.json.JsValue
import models.{Users,User}
import scala.slick.driver.H2Driver.simple._
import Database.{threadLocalSession => session}
import play.api.db.slick.DB.withSession
import play.api.Play.current

/**
 * Provide security features
 */
trait Secured { this: Controller =>  
  /**
   * Retrieve the connected user email.
   */
  private def username(request: RequestHeader) = request.session.get("email")

  /**
   * Redirect to login if the user in not authorized.
   */
  private def onUnauthorized(request: RequestHeader) = Results.Redirect(routes.Application.index(""))
  
  // --
  
  /** 
   * Action for authenticated users.
   */
  def Authenticated[T](parser: BodyParser[T])(f: => User => Request[T] => Result) = Action(parser) { request =>
    request.session.get("session") match {
      case None => Results.Unauthorized
      case session =>
        val q = for (user <- Users if user.session === session) yield user.*
        withSession { implicit session =>
          q.firstOption match {
            case None => Results.Unauthorized
            case Some(user) => f(user)(request)
          }
        }
    }    
  }
  
  def Authenticated(f: => User => Request[AnyContent] => Result): Action[AnyContent] = 
    Authenticated(parse.anyContent)(f) 

  /**
   * Check if the connected user is a member of this project.
   *
  def IsMemberOf(project: Long)(f: => String => Request[AnyContent] => Result) = IsAuthenticated { user => request =>
    if(Project.isMember(project, user)) {
      f(user)(request)
    } else {
      Results.Forbidden
    }
  }*/

  /**
   * Check if the connected user is a owner of this task.
   *
  def IsOwnerOf(task: Long)(f: => String => Request[AnyContent] => Result) = IsAuthenticated { user => request =>
    if(Task.isOwner(task, user)) {
      f(user)(request)
    } else {
      Results.Forbidden
    }
  }*/

}