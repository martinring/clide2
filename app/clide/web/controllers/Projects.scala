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
  
  def session(username: String, name: String) = ActorSocket(
      user = username,
      message = WithUser(username, StartSession(name)),
      serialize = { serialize },
      deserialize = { json =>
        (json \ "t").asOpt[String] match {
          case None => ForgetIt
          case Some(t) => t match {
            case "browse" => BrowseFolder            
          }
        }
      })
  
  def fileBrowser(username: String, name: String) = ActorSocket(
      user = username,
      message = WithUser(username,WithProject(name,StartFileBrowser)),
      serialize = { serialize },
      deserialize = { json =>
        (json \ "t").asOpt[String] match {
          case None => ForgetIt
          case Some(t) => t match {
            case "browse" => // TODO: Make this pretty!
              WithPath((json \ "path").as[Seq[String]], BrowseFolder)
            case "explore" => 
              WithPath((json \ "path").as[Seq[String]], ExplorePath)
            case "new" =>
              WithPath((json \ "path").as[Seq[String]], NewFile)
            case "open" =>
              WithPath((json \ "path").as[Seq[String]], OpenFile)
            case "touch" => 
              WithPath((json \ "path").as[Seq[String]], TouchFile)
          }
        }
      })
}