package clide.web

import play.api._
import akka.actor.ActorRef
import play.api.libs.concurrent.Akka
import akka.actor._
import scala.concurrent.duration._
import akka.util.Timeout
import scala.concurrent.Await

object Global extends GlobalSettings {
  var server: Option[ActorRef] = None
  
  override def onStart(app: Application) {    
    import clide.actors._
    Logger.info("initializing actor infrastructure")    
    val serverPath = app.configuration.getString("server-path").getOrElse {
      sys.error("No server path configured")
    }
    implicit val dispatcher = Akka.system(app).dispatcher
    val resolution = Akka.system(app).actorSelection(serverPath).resolveOne(10 seconds)
    server = Some(Await.result(resolution,10 seconds))
  }  
}