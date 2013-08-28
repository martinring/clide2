package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._
import controllers.Secured

object Projects extends Controller with Secured {
  def index(username: String) = Authenticated { user => implicit request => DB.withSession { implicit session =>
    if (user.name != username) Results.Unauthorized
    else Ok(Json.toJson(models.Projects.getForOwner(username).toSeq))
  } }
  
  def create(username: String) = Authenticated(parse.json) { user => implicit request => DB.withSession { implicit session =>
    if (user.name != username) Results.Unauthorized
    else
      (request.body \ "name").asOpt[String] match {
        case Some(name) => DB.withSession { implicit session =>
          val descr = (request.body \ "description").asOpt[String]
          val project = Project(None,name,username,descr)
          Ok(Json.toJson(models.Projects.create(project)))          
        }
        case None => BadRequest("Malformed Project")
      }
  } }    
}