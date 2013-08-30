package controllers

import play.api.mvc._
import play.api.db.slick.DB
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.libs.json._
import scala.concurrent.duration._
import models._
import org.h2.jdbc.JdbcSQLException
import play.api.libs.concurrent.Akka
import akka.util.Timeout
import scala.concurrent.ExecutionContext.Implicits.global
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import play.Logger

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
  
  def session(username: String, project: String) = WebSocket.async[JsValue] { request =>
    import infrastructure.Messages._
    implicit def error(msg: String) = new Exception(msg)
    DB.withSession { implicit session: scala.slick.driver.H2Driver.simple.Session =>
      Users.getByName(username).firstOption match {
        case None => scala.concurrent.Future.failed("user not found")
        case Some(user) => models.Projects.get(user.name, project) match {
          case None => scala.concurrent.Future.failed("project not found")
          case Some(project) =>            
            val server = Akka.system.actorFor("/user/server")
            implicit val timeout = Timeout(5 seconds)            
            for {              
              reply <- akka.pattern.ask(server,OpenSession(user,project))
            } yield reply match {
              case Welcome(ref) =>                
                val (out,channel) = Concurrent.broadcast[JsValue]
                val in = Iteratee.foreach[JsValue] { ref ! _ }
                (in,out)
            }
        }
      }    
    } 
  }
}