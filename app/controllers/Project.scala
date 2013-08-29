package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._
import org.h2.jdbc.JdbcSQLException

object Project extends Controller with Secured {
  def fileTree(username: String, project: String) = Authenticated { user => request =>
    if (username != user.name) Unauthorized
    else DB.withSession { implicit session =>
      models.Projects.get(username, project) match {
        case Some(project) =>
          val root = for {
            root <- project.root
            it <- models.Folders.get(root)
          } yield it          
          Ok(Json.toJson(root.get.toJsonTree))
        case None => NotFound
      }      
    }           
  }
}