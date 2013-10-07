package clide.web.controllers

import play.api.mvc._
import play.api.libs.json._
import clide.actors.Messages._
import clide.actors.Events._
import play.api.Logger
import clide.models.ProjectAccessLevel

object Backstage extends Controller with UserRequests {
  import clide.web.json.Conversions.serializeEvent
  
  def session(username: String) = ActorSocket(
	user = username,
	message = WithUser(username,StartBackstageSession),
	serialize = { msg => Logger.info(msg.toString); serializeEvent(msg) },
	deserialize = { json =>
	  (json \ "t").asOpt[String] match {
	    case None => ForgetIt
	    case Some(t) => t match {
	      case "init" =>
	        RequestBackstageInfo
	      case "level" =>
	        val project = (json \ "p").as[String]
	        val user    = (json \ "u").as[String]
	        val level   = (json \ "l").as[Int]
	        WithProject(project,ChangeProjectUserLevel(user,ProjectAccessLevel(level)))
	    }
	  }	        
	}
  )
}