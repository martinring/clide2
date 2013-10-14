package clide.web.controllers

import play.api.mvc._
import play.api.libs.json._
import clide.actors.Messages._
import clide.actors.Events._
import clide.web.json.Conversions._
import scala.concurrent.Future
import clide.models.ProjectAccessLevel
import clide.collaboration.Operation
import clide.collaboration.Annotations
import play.api.Logger

object Projects extends Controller with UserRequests with DefaultResults {  
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
      serialize = { msg => Logger.info(msg.toString); serializeEvent(msg) },
      deserialize = { json =>
        ((json \ "f").asOpt[Long],(json \ "r").asOpt[Long]) match {          
          case (Some(file),Some(rev)) => (json\"o").asOpt[Operation] match {
            case Some(operation) => Edit(file,rev,operation)
            case None => (json\"a").asOpt[Annotations] match {
              case Some(annotation) => Annotate(file,rev,annotation,(json\"n").as[String])
              case None => ForgetIt
            }
          }
          case _ => (json \ "t").asOpt[String] match {
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
              case "chat" =>
                Talk((json \ "to").asOpt[Long], (json \ "msg").as[String])
            }
          }
        }        
      })
  
  def fileBrowser(username: String, name: String) = ActorSocket(
      user = username,
      message = WithUser(username,WithProject(name,StartFileBrowser)),
      serialize = { serializeEvent },
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