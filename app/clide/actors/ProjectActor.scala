package clide.actors

import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._

class ProjectActor(var info: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._
    
  var root: ActorRef    = context.system.deadLetters
  var users: Map[String,ProjectAccessLevel.Value] = Map()
  
  def admin: Receive = {
    case DeleteProject =>
      DB.withSession { implicit session: Session =>
        ProjectInfos.delete(info.id)
      }
      sender         ! DeletedProject(info)
      context.parent ! DeletedProject(info)      
  }
  
  def none: Receive = {
    case _ => sender ! NotAllowed
  }
  
  def receive = {
    case WrappedProjectMessage(level,msg) => level match {
      case ProjectAccessLevel.Admin =>
        (admin orElse none)(msg)
      case _ =>
        none(msg)
    }
      
  }
  
  override def preStart() {
    log.info(s"project ${info.owner}/${info.name}")
    DB.withSession { implicit session: Session =>           
      users = ProjectAccessLevels.getProjectUsers(info.id).elements.toMap
    }
  }
}