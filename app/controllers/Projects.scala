package controllers

import play.api.mvc._
import play.api.db.slick.DB.withSession
import play.api.Play.current
import play.api.libs.json._
import models._

object Projects extends Controller with Secured {
  def index = Action { implicit request => withSession { implicit session =>
    Ok(Json.toJson(models.Projects.getForOwner("martinring").elements.toSeq))
  } }
  
  def create = Action { implicit request => withSession { implicit session =>  
    Ok("")   
  } }
}