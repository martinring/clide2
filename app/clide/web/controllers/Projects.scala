package clide.web.controllers

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
import clide.models._
import clide.actors._
import Messages._
import Events._

object Projects extends Controller with ActorAsk with Secured {  
  def index(username: String) = Authenticated { request => 
    if (request.user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      Ok(Json.toJson(ProjectInfos.getByOwner(username).toSeq))
  } }
  
  def details(username: String, project: String) = Authenticated { request =>
    if (request.user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      Ok(Json.toJson(ProjectInfos.get(username,project)))
  } }  
  
  def put(username: String) = Authenticated(parse.json) { request => 
    if (request.user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      (request.body \ "name").asOpt[String] match {
        case Some("") => Results.BadRequest("project name must not be empty!")
        case Some(name) => 
          val descr = (request.body \ "description").asOpt[String]
          val project = ProjectInfo(None,name,username,descr)
          try {
            val p = ProjectInfos.create(project)
            server ! CreatedProject(p)
            Results.Ok(Json.toJson(p))
          } catch {
            case e: JdbcSQLException => e.getErrorCode() match {
              case 23505 => Results.BadRequest("A project with that name already exists")
              case _     => Results.BadRequest(e.getMessage())                                           
          } }
        case None => Results.BadRequest("Malformed Project")      
  } } }
  
  def delete(username: String, project: String) = Authenticated(parse.empty) { request =>
    if (request.user.name != username) Results.Unauthorized
    else DB.withSession { implicit session =>
      val q = for (p <- ProjectInfos if p.ownerName === username && p.name === project) yield p      
      if (q.delete > 0) Ok
      else NotFound
  } }
  
  def session(username: String, project: String) = WebSocket.async[JsValue] { request =>
    null
    /*implicit def error(msg: String) = new Exception(msg)
    DB.withSession { implicit session: scala.slick.driver.H2Driver.simple.Session =>
      UserInfos.getByName(username).firstOption match {
        case None => scala.concurrent.Future.failed("user not found")
        case Some(user) => ProjectInfos.get(user.name, project) match {
          case None => scala.concurrent.Future.failed("project not found")
          case Some(project) => 
            val server = Akka.system.actorFor("/user/server")
            implicit val timeout = Timeout(5 seconds)
            for {
              reply <- akka.pattern.ask(server,OpenSession(user,project))
            } yield reply match {
              case ServerActor.WelcomeToSession(ref) => // The session has been opened and we get an ActorRef to the
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
                        case JsSuccess(msg,where) => ref ! msg
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
                                 .mapDone{ Unit => dolmetcher ! PoisonPill; ref ! Leave }
                (in,out)           
  } } } } }*/ }
}