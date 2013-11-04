 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.web

import play.api._
import akka.actor.ActorRef
import play.api.libs.concurrent.Akka
import akka.actor._
import scala.concurrent.duration._
import akka.util.Timeout
import scala.concurrent.Await
import scala.concurrent.Promise
import akka.pattern._
import clide.actors.util.ServerForwarder

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
object Global extends GlobalSettings {
  implicit val timeout      = Timeout(30 seconds)
  private val serverForwarder = Promise[ActorRef]()
  
  def server: ActorRef = {
    import play.api.Play.current
    implicit val dispatcher = Akka.system.dispatcher             
    Await.result(serverForwarder.future, 30 seconds)
  }
  
  override def onStart(app: Application) {
    import play.api.Play.current
    val serverPath = app.configuration.getString("server-path").get
    serverForwarder.success {
      Akka.system.actorOf(ServerForwarder(serverPath), "server")
    }
  }
}