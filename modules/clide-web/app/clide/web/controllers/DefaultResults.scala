 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.web.controllers

import clide.actors.Events._
import clide.web.json.Conversions._
import play.api.mvc._
import play.api.mvc.Results._
import play.api.libs.json.Json

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
trait DefaultResults {
  implicit def defaultResult(event: Event): SimpleResult = event match {
    case CreatedProject(info) => Ok(Json.toJson(info))
    case ProjectCouldNotBeCreated(reason) => BadRequest(reason)
    case DeletedProject(info) => Ok
    case DoesntExist => NotFound("The requested resource doesn't exist (anymore).")
    case SessionTimedOut => Unauthorized("timeout")
    case NotLoggedIn => Unauthorized("You are not logged in.")
    case NotAllowed  => Forbidden("You are not allowed to access this resource")
    case TimeOut => Results.InternalServerError("An error occurred while processing your request on the server. :(")
    case Validated(info) => Ok(Json.obj(
        "username" -> info.name, 
        "email" -> info.email))
    case UserProjectInfos(u,c) => Ok(Json.obj(
        "userProjects" -> Json.toJson(u),
        "collaborating" -> Json.toJson(c)))    
  }
}