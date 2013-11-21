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

package clide

import akka.actor._
import com.typesafe.config.ConfigFactory
import akka.kernel.Bootable
import clide.actors.UserServer
import scala.slick.session.Database
import scala.reflect.runtime.universe
import scala.slick.driver.ExtendedDriver
import clide.persistence.DAL
import scala.slick.session.Session

/**
 * This is the main entry point for the microkernel akka application. It sets up
 * the configuration and then starts an instance of a
 * [[clide.actors.UserServer `UserServer`]].
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Core extends Bootable {
  private val system   = ActorSystem("clide",ConfigFactory.load.getConfig("clide"))
  private val config   = system.settings.config

  private val profile = {
    val runtimeMirror = universe.runtimeMirror(getClass.getClassLoader)
    val module = runtimeMirror.staticModule(config.getString("db.profile"))
    runtimeMirror.reflectModule(module).instance.asInstanceOf[ExtendedDriver]
  }

  /**
   * The Data Access Layer. (see [[clide.persistence.DAL `clide.persistence.DAL`]])
   * If you are unfamiliar with slick, you should have a look at the
   * <a href='http://slick.typesafe.com/docs/'>slick documentation</a>.
   */
  lazy val DAL = new DAL(profile)

  /**
   * The database connection as configured in the `application.conf` file.
   */
  lazy val DB = slick.session.Database.forURL(
    url      = config.getString("db.url"),
    user     = config.getString("db.user"),
    password = config.getString("db.password"),
    driver   = config.getString("db.driver"))

  /**
   * Starts up the server by creating an instance of
   * [[clide.actors.UserServer `UserServer`]]
   */
  def startup() {
    val server = Some(system.actorOf(UserServer(), "users"))
  }

  /**
   * Stops the actor system (and all actors).
   *
   * @todo this should be more gentle in shutting down all actors.
   */
  def shutdown() {
    system.shutdown()
  }
}

/**
 * The CoreApp can be utilized to start an instance of the core server without
 * using akka microkernel. It defines a `main` method.
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
object CoreApp extends App {
  args match {
    case Array("schema") =>
      println("creating database schema")
      Core.DB.withSession{ implicit session: Session => Core.DAL.create }
    case _ =>
  }
  Core.startup()
  readLine()
  Core.shutdown()
}
