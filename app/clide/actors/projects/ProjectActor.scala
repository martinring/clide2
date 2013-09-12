package clide.actors.projects


import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._

class ProjectActor(var info: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
    
  var root: ActorRef    = context.system.deadLetters
  
  var users: Map[UserInfo,Int] = Map()
  
  def receive = {
    case DeleteProject => 
      DB.withSession { implicit session: Session =>
        
      }
  }
  
  override def preStart() {
    log.info(s"project ${info.owner}/${info.name}")
    DB.withSession { implicit session: Session =>           
      users = ProjectAccessInfos.getProjectUsers(info.id).elements.toMap
    }
  }
}