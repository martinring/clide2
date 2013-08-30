package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._
import org.h2.jdbc.JdbcSQLException

object Projects extends Controller with Secured {
  def index(username: String) = Authenticated { user => implicit request => 
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      Ok(Json.toJson(models.Projects.getByOwner(username).toSeq))
  } }
  
  def details(username: String, project: String) = Authenticated { user => implicit request =>
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      Ok(Json.toJson(models.Projects.get(username,project)))
    }
  }
  
  def put(username: String) = Authenticated(parse.json) { user => implicit request => 
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      (request.body \ "name").asOpt[String] match {
        case Some("") => BadRequest("project name must not be empty!")
        case Some(name) => 
          val descr = (request.body \ "description").asOpt[String]
          val project = models.Project(None,name,username,descr)
          try {
            Ok(Json.toJson(models.Projects.create(project)))
          } catch {
            case e: JdbcSQLException => e.getErrorCode() match {
              case 23505 => BadRequest("A project with that name already exists")
              case _     => BadRequest(e.getMessage())
            }                               
          }
        case None => BadRequest("Malformed Project")
      }
  } }
  
  def delete(username: String, project: String) = Authenticated { user => implicit request =>
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      val q = for (p <- models.Projects if p.ownerName === username && p.name === project) yield p      
      if (q.delete > 0) Ok
      else NotFound
  } }
  
  def session(username: String, project: String) = WebSocket.
}