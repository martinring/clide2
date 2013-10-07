package clide.web

import play.api._
import akka.actor.ActorRef
import play.api.libs.concurrent.Akka
import akka.actor._
import scala.concurrent.duration._
import akka.util.Timeout
import scala.concurrent.Await

object Global extends GlobalSettings {
  var serverPath: String = "not configured"
  
  var serverOption: Option[ActorRef] = None
  
  def server: ActorRef = serverOption.filter(!_.isTerminated) getOrElse {
    Logger.warn("server terminated")
    Logger.info("system must wait for new server connection")
    import play.api.Play.current
    val resolution = Akka.system.actorSelection(serverPath).resolveOne(10 seconds)
    serverOption = Some(Await.result(resolution, 10 seconds))
    Logger.info("reconnected")
    server
  }
  
  override def onStart(app: Application) {   
    import clide.actors._
    
    Logger.info("initializing actor infrastructure")    
    serverPath = app.configuration.getString("server-path").get            
    val resolution = Akka.system(app).actorSelection(serverPath).resolveOne(10 seconds)    
    serverOption = Some(Await.result(resolution,10 seconds))
  }  
}