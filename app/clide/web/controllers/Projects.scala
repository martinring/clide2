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
import scala.concurrent.Future

object Projects extends Controller with UserRequests {  
  def index(username: String) = UserRequest.async { request =>
    request.askFor(username)(BrowseProjects).map {
      case UserProjectInfos(own,other) =>
        Ok(Json.toJson(own))
      case other => defaultResult(other)
    }
  }     
  
  def put(username: String) = UserRequest.async(parse.json) { request =>
    Json.fromJson[CreateProject](request.body) match {
      case JsError(e) =>
        Future.successful(BadRequest("The server didn't understand your request."))
      case JsSuccess(msg,_) => request.askFor(username)(msg).map(defaultResult)
    }
  }

  def delete(username: String, name: String) = UserRequest.async(parse.empty) { request =>    
    request.askFor(username)(WithProject(name,DeleteProject)).map(defaultResult)
  }
  
  def session(username: String, name: String) = WebSocket.async[JsValue] { request =>
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