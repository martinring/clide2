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

package clide

import akka.actor._
import com.typesafe.config.ConfigFactory
import akka.kernel.Bootable
import clide.actors.UserServer
import scala.reflect.runtime.universe
import com.typesafe.config.Config
import clide.persistence.Schema
import scala.slick.driver.JdbcDriver

object Core extends Bootable {
  private var config: Config = null
  private var system: ActorSystem = null

  def startup() {
    config = ConfigFactory.load.getConfig("clide-core")
    system = ActorSystem("clide", config)
  }

  def shutdown() {
    system.shutdown()
    system.awaitTermination()
    system = null
    config = null
  }

  lazy val profile = {
    val runtimeMirror = universe.runtimeMirror(getClass.getClassLoader)
    val module = runtimeMirror.staticModule(config.getString("db.profile"))
    runtimeMirror.reflectModule(module).instance.asInstanceOf[JdbcDriver]
  }

  import profile.simple._

  /**
   * The Data Access Layer. (see [[clide.persistence.Schema `clide.persistence.Schema`]])
   * If you are unfamiliar with slick, you should have a look at the
   * <a href='http://slick.typesafe.com/docs/'>slick documentation</a>.
   */
  lazy val schema = new Schema(profile)

  /**
   * The database connection as configured in the `application.conf` file.
   */
  lazy val db = Database.forURL(
    url      = config.getString("db.url"),
    user     = config.getString("db.user"),
    password = config.getString("db.password"),    
    driver   = config.getString("db.driver"))

  /**
   * Starts up the server by creating an instance of
   * [[clide.actors.UserServer `UserServer`]]
   */
  def createUserServer() = {
    // FIXME: createAll must be working again
    //db.withSession{ implicit session: Session => schema.createAllIfNotExist() }
    if (system == null) sys.error("system uninitialized")
    system.actorOf(UserServer.props, "users")
  }
}

/**
 * The CoreApp can be utilized to start an instance of the core server without
 * using akka microkernel. It defines a `main` method.
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
object CoreApp extends App {
  Core.startup()
  Core.shutdown()
}
