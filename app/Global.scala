import play.api._
import play.api.db.DB
import play.api.Play.current
import scala.slick.session.{Database,Session}
import scala.slick.session.Database.{threadLocalSession => session}
import scala.slick.driver.H2Driver.simple._

object Global extends GlobalSettings {
  override def onStart(app: Application) {    
    lazy val database = Database.forDataSource(DB.getDataSource())
    /*play.api.db.slick.DB.withSession { implicit session =>
      models.Projects.insertAll(models.Project(0,"test","martinring"), models.Project(1,"blubb","martinring"))
    }*/
  }
  
  override def onStop(app: Application) {
  }
}