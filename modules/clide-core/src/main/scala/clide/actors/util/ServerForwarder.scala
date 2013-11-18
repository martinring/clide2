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
package clide.actors.util

import akka.actor._
import scala.concurrent.duration._
import scala.language.postfixOps

/**
 * A [[ServerForwarder]] serves as a utility actor for connected systems, which
 * handles the connection to the specified server path and automatically
 * reconnects upon failure.
 *
 * The intended scenario is to connect it to the central `UserServer` running
 * on the core server. It can then be instantly used as if it was a direct
 * reference to the server, even if the server isn't started up yet or failed.
 *
 * {{{
 * val server = actorOf(ServerForwarder(serverPath), "server")
 * server ! SignUp("martinring","martin.ring@dfki.de","banana")
 * }}}
 *
 * Note: Message Timeouts can be infinite and have to be handled by the user if
 * desired.
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
object ServerForwarder {
  /**
   * Create the `Props` for a new `ServerForwarder`.
   * @param path
   *   The full actor path of the server
   *   (i.e. `"akka.tcp://clide@127.0.0.1:9001/user/users"`)
   */
  def apply(path: String) = Props(classOf[ServerForwarder], path)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class ServerForwarder(path: String) extends Actor with Stash with ActorLogging {
  def receive = connecting

  def connect() {
    log.info("connecting to server at {}", path)
    context.actorSelection(path) ! Identify("server")
  }

  def connecting: Receive = {
    connect()
    context.setReceiveTimeout(4 seconds)

    {
      case ActorIdentity("server",Some(ref)) =>
        context.become(connected(ref))
      case ActorIdentity("server",None) =>
      case ReceiveTimeout => connect()
      case _ => stash()
    }
  }

  def connected(server: ActorRef): Receive = {
    log.info("connected")
    context.watch(server)
    context.setReceiveTimeout(Duration.Undefined)
    unstashAll()

    {
      case Terminated(`server`) =>
        context.become(connecting)
      case ActorIdentity("server",_) =>
      case msg =>
        server forward msg
    }
  }
}
