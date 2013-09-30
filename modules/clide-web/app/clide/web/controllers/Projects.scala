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
import clide.collaboration.{Operation,Annotations}

object Projects extends Controller with UserRequests {  
  def index(username: String) = UserRequest.async { request =>
    request.askFor(username)(BrowseProjects).map(defaultResult)    
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
  
  def invite(username: String, name: String) = UserRequest.async(parse.json) { request =>
    request.askFor(username)(WithUser((request.body \ "user").as[String],Invite(name))).map(defaultResult)
  }
  
  def session(username: String, name: String) = ActorSocket(
      user = username,
      message = WithUser(username,WithProject(name,StartSession)),
      serialize = { msg => Logger.info(msg.toString); serialize(msg) },
      deserialize = { json =>
        (json \ "r").asOpt[Long] match {
          case None => (json \ "t").asOpt[String] match {
	        case None => ForgetIt
	        case Some(t) => t match {
	          case "init" => 
	            RequestSessionInfo
	          case "open" =>
	            SwitchFile((json \ "id").as[Long])
	          case "close" =>
	            CloseFile((json \ "id").as[Long])
	          case "color" =>
	            SetColor((json \ "c").as[String])
	          case "invite" =>
	            ChangeProjectUserLevel((json \ "u").as[String], ProjectAccessLevel.Write)
	        }
	      }
          case Some(rev) => (json\"o").asOpt[Operation] match {
            case Some(operation) => Edit(rev,operation)
            case None => (json\"a").asOpt[Annotations] match {
              case Some(annotation) => Annotate(rev,annotation)
              case None => ForgetIt
            }
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
            case "touchFile" => 
              WithPath((json \ "path").as[Seq[String]], TouchFile)
            case "touchFolder" => 
              WithPath((json \ "path").as[Seq[String]], TouchFolder)
            case "rm" =>
              WithPath((json \ "path").as[Seq[String]], Delete)
          }
        }
      })
}