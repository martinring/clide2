package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._
import org.h2.jdbc.JdbcSQLException


/**
 * TODO: User rights are ignored right now!!!
 */
object Files extends Controller with Secured {
  def getFiles(id: Long) = Authenticated { user => request => 
    DB.withSession { implicit session =>
      models.Folders.get(id) match {
        case None => NotFound
        case Some(f) => Ok(Json.toJson(f.toJsonTree))
      }                   
    }
  }
  
  def newFolder(parent: Long, name: String) = Authenticated { user => request =>
    DB.withSession { implicit session =>
      try { 
        Ok(Json.toJson(models.Folders.create(Folder(None,name,Some(parent)))))
      } catch {
        case e: JdbcSQLException =>
          BadRequest(e.getMessage())
      }
    }
  }
}