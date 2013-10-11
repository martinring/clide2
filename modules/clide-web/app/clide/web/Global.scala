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
      Akka.system.actorOf(Props(classOf[clide.actors.util.ServerForwarder], serverPath), "server-forwarder")
    }
  }
}