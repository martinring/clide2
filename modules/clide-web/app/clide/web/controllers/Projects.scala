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

import scala.concurrent.Future

import clide.actors.Messages._
import clide.collaboration.Annotations
import clide.collaboration.Operation
import clide.models.ProjectAccessLevel
import clide.web.json.Conversions._
import play.api.Logger
import play.api.libs.json._
import play.api.mvc._

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

  def backstageSession(username: String) = {
    Logger.info("preparing actor socket for backstage")
    ActorSocket( 
      user = username,
      message = WithUser(username,StartBackstageSession),
      serialize = serializeEvent,
      deserialize = { json =>
        (json \ "t").asOpt[String] match {
          case Some("init") =>
            Logger.info("init message for backstage")
            BrowseProjects
          case _ =>
            Logger.warn("didn't understand: " + json.toString)
            ForgetIt
        }
      })}

  def session(username: String, name: String) = ActorSocket(
      user = username,
      message = WithUser(username,WithProject(name,StartSession)),
      serialize = serializeEvent,
      deserialize = { json =>
        ((json \ "f").asOpt[Long],(json \ "r").asOpt[Long]) match {
          case (Some(file),Some(rev)) => (json\"o").asOpt[Operation] match {
            case Some(operation) => Edit(file,rev,operation)
            case None => (json\"a").asOpt[Annotations] match {
              case Some(annotation) => Annotate(file,rev,annotation,(json\"n").as[String])
              case None =>
                Logger.warn("didn't understand: " + json.toString)
                ForgetIt
            }
          }
          case _ => (json \ "t").asOpt[String] match {
            case None =>
              Logger.warn("didn't understand: " + json.toString)
              ForgetIt
            case Some(t) => t match {
              case "init" =>
                Logger.info("got init")
                RequestSessionInfo
              case "open" =>
                OpenFile((json \ "id").as[Long])
              case "close" =>
                CloseFile((json \ "id").as[Long])
              case "kick" =>
                Kick((json \ "s").as[Long])
              case "color" =>
                SetColor((json \ "c").as[String])
              case "looking" =>
                LookingAtFile((json \ "f").as[Long])
              case "ignoring" =>
                StoppedLookingAtFile((json \ "f").as[Long])
              case "eof" =>
                EOF
              case "invite" =>
                ChangeProjectUserLevel((json \ "u").as[String], ProjectAccessLevel.Write)
              case "chat" =>
                Talk((json \ "to").asOpt[Long], (json \ "msg").as[String], (json \ "tp").asOpt[String])
              case _ =>
                Logger.warn("didn't understand: " + json.toString)
                ForgetIt
            }
          }
        }
      })

  def fileBrowser(username: String, name: String) = ActorSocket(
      user = username,
      message = WithUser(username,WithProject(name,StartFileBrowser)),
      serialize = serializeEvent,
      deserialize = { json =>
        (json \ "t").asOpt[String] match {
          case None =>
            Logger.warn("didn't understand: " + json.toString)
            ForgetIt
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
