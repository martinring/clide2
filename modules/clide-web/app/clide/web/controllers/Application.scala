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

import java.util.UUID
import scala.concurrent.duration.DurationInt
import akka.actor.ActorDSL._
import akka.actor.actorRef2Scala
import play.api.Play
import play.api.Play.current
import play.api.Routes
import play.api.libs.concurrent.Akka
import play.api.libs.concurrent.Akka.system
import play.api.libs.iteratee._
import play.api.libs.json._
import play.api.mvc._
import akka.actor.ActorRef
import clide.models._
import clide.actors.Events._
import clide.actors.Messages._
import scala.concurrent.Future

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Application extends Controller with UserRequests {
  def index(path: String) = UserRequest.async { implicit request =>
    def notLoggedIn: Result = path match {
      case "login" => Ok(clide.web.views.html.index()).withNewSession
      case _       => Redirect("/login").withNewSession
    }
    request.ask(Validate).map {
      case Validated(info) =>
        if (path.isEmpty()) Redirect(s"${info.name}/backstage")
        else if (path == "login") Ok(clide.web.views.html.index()).withNewSession else Ok(clide.web.views.html.index())
      case _               => notLoggedIn
    }
  }

  // -- Javascript routing
  def javascriptRoutes = Action { implicit request =>
    import routes.javascript._
      Ok(
        Routes.javascriptRouter("jsRoutes")(
          routes.javascript.Application.index,
          routes.javascript.Authentication.login,
          routes.javascript.Authentication.logout,
          routes.javascript.Authentication.validateSession,
          routes.javascript.Authentication.signup,
          routes.javascript.Projects.index,
          routes.javascript.Projects.backstageSession,
          routes.javascript.Projects.put,
          routes.javascript.Projects.delete,
          routes.javascript.Projects.session,
          routes.javascript.Projects.fileBrowser
        )
      ).as("text/javascript")
  }
}
