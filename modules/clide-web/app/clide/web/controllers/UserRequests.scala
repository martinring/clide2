 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 **                                                                           **
 **  This file is part of Clide.                                              **
 **                                                                           **
 **  Clide is free software: you can redistribute it and/or modify            **
 **  it under the terms of the GNU General Public License as published by     **
 **  the Free Software Foundation, either version 3 of the License, or        **
 **  (at your option) any later version.                                      **
 **                                                                           **
 **  Clide is distributed in the hope that it will be useful,                 **
 **  but WITHOUT ANY WARRANTY; without even the implied warranty of           **
 **  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
 **  GNU General Public License for more details.                             **
 **                                                                           **
 **  You should have received a copy of the GNU General Public License        **
 **  along with Clide.  If not, see <http://www.gnu.org/licenses/>.           **
 \*                                                                           */

package clide.web.controllers

import akka.util.Timeout
import scala.concurrent.duration._
import play.api.Play.current
import scala.concurrent.Future
import clide.actors.Messages._
import clide.actors.Events._
import play.api.mvc._
import scala.concurrent.Future
import play.api.libs.json._
import play.api.libs.iteratee.Iteratee
import java.util.concurrent.TimeoutException
import play.core.server.websocket.FrameFormatter
import play.core.server.websocket.FrameFormatter
import play.api.libs.iteratee.Concurrent
import akka.actor._
import akka.actor.ActorDSL._
import play.api.Logger
import scala.util.Success
import scala.util.Failure
import play.api.libs.iteratee.Enumerator
import play.api.libs.concurrent.Akka
import scala.language.implicitConversions
import scala.language.postfixOps

trait UserRequests { this: Controller =>
  implicit val timeout = Timeout(2.5 seconds)
  implicit def ask(act: ActorRef) = akka.pattern.ask(act)
  implicit val system = play.api.libs.concurrent.Akka.system
  implicit val executionContext = play.api.libs.concurrent.Akka.system.dispatcher

  def server = clide.web.Global.server

  val Messages = clide.actors.Messages

  class UserAskRequest[A](val ask: (UserMessage => Future[Event]),
                          val askFor: (String => UserMessage => Future[Event]),
                          request: Request[A])
    extends WrappedRequest[A](request)

  def ActorSocket(
      user: String,
      message: UserMessage,
      deserialize: JsValue => Message,
      serialize: Event => JsValue) = WebSocket.async[JsValue] { request =>
    val auth = for {
      user <- request.session.get("user")
      key  <- request.session.get("key")
    } yield (user,key)

    val req: Message = auth match {
      case None             => AnonymousFor(user,message)
      case Some((user,key)) => IdentifiedFor(user,key,message)
    }

    val mediator = system.actorOf(Props[WebsocketMediator])

    val f = (mediator ? WebsocketMediator.Init(server,req)).mapTo[Enumerator[Event]]

    val in = Iteratee.foreach[JsValue](j => mediator ! deserialize(j)).map(Unit => mediator ! EOF)

    f.map { out =>
      (in,out.map(serialize))
    }.recover {
      case e =>
        (Iteratee.ignore[JsValue], Enumerator[JsValue](Json.obj("t"->"e","c"->e.getMessage)).andThen(Enumerator.eof))
    }
  }

  object UserRequest extends ActionBuilder[UserAskRequest] {
    def invokeBlock[A](request: Request[A], block: UserAskRequest[A] => Future[SimpleResult]) = {
      val auth = for {
        user <- request.session.get("user")
        key  <- request.session.get("key")
      } yield (user,key)
      val ask_ : UserMessage => Future[Event] = auth match {
        case None => msg: UserMessage =>
          Future.successful(NotLoggedIn)
        case Some((user,key)) => msg: UserMessage =>
          (server ? IdentifiedFor(user,key,msg)).mapTo[Event].recover{
            case e: TimeoutException => TimeOut
          }(executionContext)
      }
      val askFor_ : String => UserMessage => Future[Event] = auth match {
        case None => user: String => msg: UserMessage =>
          (server ? AnonymousFor(user, msg)).mapTo[Event].recover{
            case e: TimeoutException => TimeOut
          }(executionContext)
        case Some((user,key)) => user: String => msg: UserMessage =>
          (server ? IdentifiedFor(user,key,WithUser(user,msg))).mapTo[Event].recover{
            case e: TimeoutException => TimeOut
          }(executionContext)
      }
      block(new UserAskRequest(ask_,askFor_,request))
    }
  }
}
