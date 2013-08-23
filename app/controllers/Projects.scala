package controllers

import play.api.mvc._
import play.api.db.slick.DB.withSession
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._

object Projects extends Controller with Secured {
  def index(username: String) = Authenticated { user => implicit request => withSession { implicit session =>
    if (user.name != username) Results.Unauthorized
    else
      Ok(Json.toJson(models.Projects.getForOwner(username).elements.toSeq))
  } }
  
  def create(username: String) = Authenticated(parse.json) { user => implicit request => withSession { implicit session =>
    if (user.name != username) Results.Unauthorized
    else
      (request.body \ "name").asOpt[String] match {
        case Some(name) => withSession { implicit session =>
          val descr = (request.body \ "description").asOpt[String]
          val project = Project(None,name,descr,username)
          val id = models.Projects.autoinc.insert(Project(None,name,descr,username))
          Ok(Json.toJson(project.copy(id = Some(id))))          
        }
        case None => BadRequest("Malformed Project")
      }
  } }
}