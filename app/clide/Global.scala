package clide

import play.api._
import play.api.db.DB
import play.api.Play.current
import scala.slick.session.Database
import scala.slick.driver.H2Driver.simple._
import play.api.libs.concurrent.Akka
import akka.actor.Props
import clide.actors.Infrastructure

object Global extends GlobalSettings {    
  override def onStart(app: Application) {    
    import clide.actors._
    Logger.info("initializing actor infrastructure")    
    Infrastructure.projectServer = Akka.system.actorOf(Props[ProjectServer], "projects")
    Infrastructure.userServer = Akka.system.actorOf(Props[UserServer], "users")
    Infrastructure.server = Akka.system.actorOf(Props[Server], "server")
  }
  
  override def onStop(app: Application) {
    
  }
}