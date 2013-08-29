package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import models._
import org.h2.jdbc.JdbcSQLException
import java.io.File
import play.api.Play


/**
 * TODO: User rights are ignored right now!!!
 */
object Files extends Controller with Secured {
  def getTree(username: String, project: String) = Authenticated { user => request =>
    if (user.name != username) Unauthorized
    else DB.withSession { implicit session =>
      models.Projects.get(username,project) match {
        case None => NotFound
        case Some(p) =>
          val l = Play.getFile(p.root).getAbsolutePath().length()          
          def jsonify(file: File): JsObject = {            
            if (file.isDirectory()) {
              val (folders,files) = file.listFiles.partition(_.isDirectory())
              val sorted = folders.sortBy(_.getName()) ++
                           files.sortBy(_.getName())
              Json.obj("name" -> file.getName(),
                       "path" -> file.getAbsolutePath().drop(l),                       
                       "files" -> sorted.map(jsonify))
            }
            else
              Json.obj("name" -> file.getName(),
                       "path" -> file.getAbsolutePath().drop(l))
          }
          Ok(jsonify(Play.getFile(p.root)))
      }
    }
  }
    
  def newFolder(username: String, project: String, path: String) = Authenticated { user => request =>
    if (user.name != username) Unauthorized
    else DB.withSession { implicit session =>
      models.Projects.get(username,project) match {
        case None => NotFound
        case Some(p) =>
          val file = Play.getFile(p.root + path + "/" + request.body.asText.get)
          if (file.exists())
            BadRequest("allready exists!")
          else {
            if (file.mkdir())
              Ok
            else
              BadRequest("could not create folder")
          }
      }
    }
  }
}