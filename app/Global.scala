import play.api._
import play.api.db.DB
import play.api.Play.current
import scala.slick.session.{Database,Session}
import scala.slick.session.Database.{threadLocalSession => session}
import scala.slick.driver.H2Driver.simple._
import play.api.libs.concurrent.Akka
import akka.actor.Props
import infrastructure.ServerActor

object Global extends GlobalSettings {  
  override def onStart(app: Application) {    
    lazy val database = Database.forDataSource(DB.getDataSource())
    Logger.info("creating infrastructure server actor")
    val server = Akka.system.actorOf(Props[ServerActor], "server")
  }
  
  override def onStop(app: Application) {
    
  }
}