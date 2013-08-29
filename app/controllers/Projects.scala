package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._

object Projects extends Controller with Secured {
  def index(username: String) = Authenticated { user => implicit request => 
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      Ok(Json.toJson(models.Projects.getForOwner(username).toSeq))
  } }
  
  def put(username: String) = Authenticated(parse.json) { user => implicit request => 
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      (request.body \ "name").asOpt[String] match {
        case Some(name) => 
          val descr = (request.body \ "description").asOpt[String]
          val project = Project(None,name,username,descr)
          Ok(Json.toJson(models.Projects.create(project)))        
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
}