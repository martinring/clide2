package clide.web.controllers

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
import views.html.defaultpages.unauthorized
import clide.db


/**
 * TODO: User rights are ignored right now!!!
 */
object Files extends Controller with Secured {    
  def getTree(username: String, project: String) = Authenticated { request =>
    if (request.user.name != username) Unauthorized
    else DB.withSession { implicit session =>
      db.Projects.get(username,project) match {
        case None => NotFound
        case Some(p) =>
          val l = Play.getFile(p.root).getAbsolutePath().length()          
          def jsonify(file: File): JsObject = {            
            if (file.isDirectory()) {
              val (folders,files) = file.listFiles.partition(_.isDirectory())
              val sorted = folders.sortBy(_.getName()) ++
                           files.sortBy(_.getName())
              Json.obj("name" -> file.getName(),
                       "path" -> file.getAbsolutePath().drop(l).replace('\\','/'),                       
                       "files" -> sorted.map(jsonify))
            }
            else
              Json.obj("name" -> file.getName(),
                       "path" -> file.getAbsolutePath().drop(l).replace('\\','/'))
          }
          Ok(jsonify(Play.getFile(p.root)))
      }
    }
  }
    
  def newFile(username: String, project: String, path: String = "") = Authenticated(parse.json) { request =>
    if (request.user.name != username) Unauthorized
    else DB.withSession { implicit session =>
      val folder = ( request.body \ "files" ).asOpt[Array[JsValue]].isDefined
      ( request.body \ "name" ).asOpt[String] match {
        case None => BadRequest("please enter a name")
        case Some("") => BadRequest("name must not be empty")
        case Some(name) => db.Projects.get(username,project) match {
          case None => NotFound("invalid project")
          case Some(p) =>   
            val l = Play.getFile(p.root).getAbsolutePath().length()    
	        val file = Play.getFile(p.root + path + "/" + name)
	        if (file.exists())
	          BadRequest("a file with that name already exists here")
	        else if (folder){
	          if (file.mkdir()) Ok(Json.obj("name" -> file.getName(), 
	                                        "path" -> file.getAbsolutePath().drop(l).replace('\\','/'), 
	                                        "files" -> Array[String]()))
	          else BadRequest("could not create folder")
	        } else {
	          if (file.createNewFile()) Ok(Json.obj("name" -> file.getName(),
	                                                "path" -> file.getAbsolutePath().drop(l).replace('\\','/')))    
	          else BadRequest("could not create file")
  } } } } }
  
  def deleteFile(username: String, project: String, path: String) = Authenticated { request =>
    if (request.user.name != username) Unauthorized
    else DB.withSession { implicit session => db.Projects.get(username,project) match {
      case None => NotFound("invalid project")
      case Some(p) =>
        val file = Play.getFile(p.root + path)
        if (!file.exists())
          NotFound("no such file")
        else {
          if (file.delete()) Ok
          else BadRequest(f"could not delete '$path'") 
  } } } }
}