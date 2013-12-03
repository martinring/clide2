/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
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

import play.api.mvc.{Controller,Action}
import play.api.Play.current
import play.api.data.Form
import play.api.data.Forms._
import play.api.libs.json._
import play.api.libs.Crypto
import java.util.UUID
import clide.models._
import scala.concurrent.Future
import clide.actors.Messages._
import clide.actors.Events._
import play.api.mvc.Results
import play.Logger
import views.html.defaultpages.badRequest

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Authentication extends Controller with UserRequests {
  // -- Authentication
  val loginForm = Form(
    tuple(
      "username" -> text,
      "password" -> text
    )
  )

  // -- Signup
  val signupForm = Form(tuple(
    "username" -> text,
    "email" -> email,
    "password" -> text(minLength=8)
  ))

  /**
   * Handle login form submission.
   */
  def login = UserRequest.async(parse.json) { implicit request =>
    loginForm.bind(request.body).fold(
      formWithErrors => Future.successful(BadRequest(formWithErrors.errorsAsJson)),
      { case (name,password) => // We assume that users logging in via web interface are humans
        request.askFor(name)(Login(password,isHuman = true)).map {
          case LoggedIn(user,login) =>
            Ok(Json.obj(
                "username" -> user.name,
                "email" -> user.email)
            ).withSession(
                "user" -> login.user,
                "key"  -> login.key
            )
          case DoesntExist =>
            Status(401)(Json.obj("username" -> Json.arr("we don't know anybody by that name")))
          case WrongPassword =>
            Status(401)(Json.obj("password" -> Json.arr("invalid password")))
          case other =>
            Status(500)(other.toString)
        }
    })
  }

  def signup = Action.async(parse.json) { implicit request =>
    signupForm.bind(request.body).fold(
      formWithErrors => Future.successful(BadRequest(formWithErrors.errorsAsJson)),
      { case (name,email,password) =>
        (server ? SignUp(name,email,password)).map {
          case SignedUp(user) =>
            Ok("Your account has been created. Have fun!")
          case other => Status(500)(other.toString)
        }
      })
  }

  def validateSession = UserRequest.async { request =>
    request.ask(Validate) map {
      case Validated(user) => Ok(Json.obj(
          "username" -> user.name,
          "email" -> user.email))
      case other => BadRequest(other.toString) // TODO: Differentiate
    }
  }

  def logout = UserRequest.async { implicit request =>
    request.ask(Logout) map {
      case LoggedOut(user) => Ok.withNewSession
      case SessionTimedOut => Ok.withNewSession // no need to confuse the user
                                                // here
      case NotLoggedIn     => Results.Unauthorized
      case DoesntExist     => Results.NotFound
      case _               => Results.InternalServerError
    }
  }
}
