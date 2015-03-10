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

package clide.web

import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration.DurationInt
import scala.language.postfixOps
import akka.actor.ActorRef
import akka.util.Timeout
import play.api.Application
import play.api.GlobalSettings
import play.api.Play.current
import play.api.libs.concurrent.Akka
import clide.Core
import play.api.Logger

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Global extends GlobalSettings {
  private var serverRef: ActorRef = null
  def server = if (serverRef == null) {
    Logger.info("creating user server")
    serverRef = Core.createUserServer()
    serverRef
  } else serverRef

  override def beforeStart(app: Application) {
    Core.startup()
  }

  override def onStop(app: Application) {
    val x = new blub.External.P("Hallo")
    //println(4 + x)
    Core.shutdown()
    serverRef = null
  }
}
