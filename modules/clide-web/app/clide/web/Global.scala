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
  private val serverMonitor = Promise[ActorRef]()
  
  def server: ActorRef = {
    import play.api.Play.current
    implicit val dispatcher = Akka.system.dispatcher
    val resolution = serverMonitor.future.flatMap(ref => ask(ref,ServerMonitor.Request))      
    Await.result(resolution.mapTo[ServerMonitor.Reply].map(_.ref), 30 seconds)
  }
  
  override def onStart(app: Application) {
    import play.api.Play.current
    val serverPath = app.configuration.getString("server-path").get
    serverMonitor.success {
      Akka.system.actorOf(Props(classOf[ServerMonitor], serverPath), "server-monitor")
    }
  }
}