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
package clide.actors

import akka.actor._
import clide.models._
import java.net.URLEncoder

/**
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
object UserServer {
  private[clide] def props = Props(classOf[UserServer])

  case class Forward(name: String, msg: Messages.Message)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class UserServer extends Actor with ActorLogging {
  import clide.Core.{ db => DB }
  import clide.Core.schema._
  import clide.Core.profile.simple._  
  import Messages.internal._
  import Messages._
  import Events._

  var users: Seq[UserInfo with Password] = Seq.empty

  def receive = {
    case SignUp(name,email,password) =>
      var errors = Map.empty[String,String]
      if (name == "")
        errors += "name" -> "error.required"
      if (password.length < 8)
        errors += "password" -> "error.minLength(8)"
      if (email.length < 4 || !email.contains('@'))
        errors += "email" -> "error.email"
      if (errors.nonEmpty)
        sender ! ActionFailed(errors)
      else {
        log.info("attempting to sign up")
        val user = UserInfo(name,email).withPassword(password)
        DB.withSession { implicit s: Session =>
          if (UserInfos.get(user.name).isDefined) {
            sender ! ActionFailed(Map("name" -> "error.unique"))
          } else if (UserInfos.getByEmail(user.email).isDefined) {
            sender ! ActionFailed(Map("email" -> "error.unique"))
          } else {
            UserInfos.insert(user)
            context.actorOf(UserActor.props(user), URLEncoder.encode(user.name,"UTF-8"))
            sender ! SignedUp(user)
	        context.system.eventStream.publish(SignedUp(user))
          }
        }
      }

    case IdentifiedFor(name,key,message) =>
      context.child(URLEncoder.encode(name,"UTF-8")) match {
        case None      => sender ! DoesntExist
        case Some(ref) =>
          ref.forward(Identified(key,message))
      }

    case AnonymousFor(name,message) =>
      context.child(URLEncoder.encode(name,"UTF-8")) match {
        case None => sender ! DoesntExist
        case Some(ref) =>
          ref.forward(Anonymous(message))
      }

    // Name resoultion here, to support distributed hierarchy in the future
    case UserServer.Forward(name, msg) =>
      context.child(URLEncoder.encode(name,"UTF-8")) match {
        case None =>
          sender ! DoesntExist
        case Some(ref) =>
          ref.forward(msg)
      }
  }

  override def preStart() {
    log.info("creating user actors")
    DB.withSession { implicit session: Session =>
      users = UserInfos.getAll.toList
    }
    users.foreach { user => context.actorOf(UserActor.props(user), URLEncoder.encode(user.name,"UTF-8")) }
    log.info("waiting for requests")
  }
}
