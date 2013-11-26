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

import akka.actor._
import play.api.libs.iteratee._
import clide.actors.Events._
import clide.actors.Messages._
import akka.pattern.ask
import scala.concurrent.duration._
import akka.util.Timeout
import scala.util.Success
import scala.util.Failure
import play.api.Logger
import scala.concurrent.duration._

object WebsocketMediator {
  case class Init(ref: ActorRef, msg: Message)
}

class WebsocketMediator extends Actor with ActorLogging {
  val (out,channel) = Concurrent.broadcast[Event]
  var peer   = context.system.deadLetters
  var client = context.system.deadLetters

  def receive = {
    case WebsocketMediator.Init(ref,message) =>
      client = sender
      ref ! message
    case EventSocket(peer,_) =>
      log.info("forwarding event socket")
      this.peer = peer
      context.watch(peer)
      client ! out    
    case e: Event =>
      log.info(e.toString())
      channel.push(e)
    case msg: Message =>
      log.info(msg.toString())
      peer ! msg
    case Terminated(ref) =>
      log.info("terminated")
      peer ! EOF
      channel.eofAndEnd()
      context.stop(self)    
  }
}
