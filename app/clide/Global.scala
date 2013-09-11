package clide

import play.api._
import play.api.db.DB
import play.api.Play.current
import scala.slick.session.Database
import scala.slick.driver.H2Driver.simple._
import play.api.libs.concurrent.Akka
import akka.actor.Props
import clide.infrastructure.ServerActor

object Global extends GlobalSettings {    
  override def onStart(app: Application) {    
    import clide.actors._
    Logger.info("initializing actor infrastructure")
    Akka.system.actorOf(Props[FileServer], "files")    
    Akka.system.actorOf(Props[ProjectServer], "projects")    
    Akka.system.actorOf(Props[UserServer], "users")
    Server.instance = Akka.system.actorOf(Props[Server], "server")
  }
  
  override def onStop(app: Application) {
    
  }
}