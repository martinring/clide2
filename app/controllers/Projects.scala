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
import akka.actor.PoisonPill
import akka.actor.ActorDSL._
import akka.actor.ActorRefFactory
import infrastructure.ServerActor

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
  } }  
  
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
          } }
        case None => BadRequest("Malformed Project")      
  } } }
  
  def delete(username: String, project: String) = Authenticated { user => implicit request =>
    if (user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      val q = for (p <- models.Projects if p.ownerName === username && p.name === project) yield p      
      if (q.delete > 0) Ok
      else NotFound
  } }
  
  def session(username: String, project: String) = WebSocket.async[JsValue] { request =>
    import infrastructure.SessionActor._
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
              reply <- akka.pattern.ask(server,ServerActor.OpenSession(user,project))
            } yield reply match {
              case ServerActor.Welcome(ref) => // The session has been opened and we get an ActorRef to the
                                   // actor, that is responsible for us.
                Logger.info("Connecting to WebSocket")
                implicit val sys = Akka.system
                // `out` is the outbound channel of our WebSocket. Messages can be pushed via 
                // channel.
                val (out,channel) = Concurrent.broadcast[JsValue]
                // We instantiate an intermediate Actor, that translates between JSON and 
                // Scala objects.
                val dolmetcher = actor(new Act { become {
                    case json: JsValue =>
                      Json.fromJson[Request](json) match {
                        case JsSuccess(msg,where) => sys.actorFor(ref) ! msg
                        case JsError(e)           => channel.push(Json.obj("error" -> e.toString))
                      }                      
                    case reply: Reply  =>                      
                      channel.push(Json.toJson(reply))                    
                } }) 
                // `in` is the inbound channel of the WebSocket. Messages get forwarded to the
                // dolmetcher actor which then passes them to the responsible session actor.
                // when the socket is closed, we send a PoisonPill to the dolmetcher and a
                // close notification directly to the session actor.
                val in = Iteratee.foreach[JsValue]{ dolmetcher ! _ }
                                 .mapDone{ Unit => dolmetcher ! PoisonPill; sys.actorFor(ref) ! CloseSession }
                (in,out)           
  } } } } }
}