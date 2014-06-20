/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */

package clide.web.controllers

import scala.language.implicitConversions

import clide.actors.Events._
import clide.web.json.Conversions.ProjectInfoWrites
import play.api.libs.json.Json
import play.api.libs.json.Json.toJsFieldJsValueWrapper
import play.api.mvc.Results._
import play.api.mvc.Result

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
trait DefaultResults {
  implicit def defaultResult(event: Event): Result = event match {
    case CreatedProject(info) => Ok(Json.toJson(info))
    case ProjectCouldNotBeCreated(reason) => BadRequest(reason)
    case DeletedProject(info) => Ok
    case DoesntExist => NotFound("The requested resource doesn't exist (anymore).")
    case SessionTimedOut => Unauthorized("timeout")
    case NotLoggedIn => Unauthorized("You are not logged in.")
    case NotAllowed  => Forbidden("You are not allowed to access this resource")
    case TimeOut => InternalServerError("An error occurred while processing your request on the server. :(")
    case Validated(info) => Ok(Json.obj(
        "username" -> info.name,
        "email" -> info.email))
    case UserProjectInfos(u,c) => Ok(Json.obj(
        "userProjects" -> Json.toJson(u),
        "collaborating" -> Json.toJson(c)))
  }
}
