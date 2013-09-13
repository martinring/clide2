package clide.actors

import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._
import clide.actors.files._

class ProjectActor(var info: ProjectInfo) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._
    
  var root: ActorRef    = context.system.deadLetters  
  
  def admin: Receive = {
    case DeleteProject =>
      DB.withSession { implicit session: Session =>
        ProjectInfos.delete(info.id)
      }
      sender         ! DeletedProject(info)
      context.parent ! DeletedProject(info)
      context.stop(self)
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
    root = context.actorOf(Props(classOf[FolderActor], info, None, "files"),"files")
    log.info(s"project ${info.owner}/${info.name}")
  }
}