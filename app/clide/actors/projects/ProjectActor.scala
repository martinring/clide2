package clide.actors.projects


import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._

class ProjectActor(id: Long) extends Actor with ActorLogging {
  import clide.actors.Messages._
  
  var info: ProjectInfo = null
  var root: ActorRef    = context.system.deadLetters
  
  def receive = {
    case fm: FileMessage => 
  }
  
  override def preStart() {
    DB.withSession { implicit session: Session =>
      ProjectInfos.get(id).firstOption match {
        case None       => 
          log.error("this project doesn't exist")
          context.stop(self)
        case Some(info) => 
          this.info = info
          log.info(s"project ${info.owner}/${info.name}")
      }
    }    
  }
}