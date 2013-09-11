package clide.actors

import scala.slick.driver.H2Driver.simple._
import akka.actor.Actor
import play.api.Play.current
import play.api.db.slick.DB
import akka.actor.Props
import akka.actor.ActorLogging
import java.net.URLEncoder
import clide.models._
import akka.actor.PoisonPill
import scala.slick.session.Session

object ProjectServer {
  trait Message
  case object Initialize extends Message
  case class CreateProject(user: UserInfo, name: String, description: Option[String] = None) extends Message
  case class DeleteProject(project: ProjectInfo) extends Message  
  
  trait ProjectEvent
  case class CreatedProject(project: ProjectInfo) extends ProjectEvent
  case class DeletedProject(project: ProjectInfo) extends ProjectEvent  
}

class ProjectServer extends Actor with ActorLogging {
  import ProjectServer._
  import projects._
  
  def getProject(project: ProjectInfo) = context.child(project.actorName).getOrElse {
    context.actorOf(Props(classOf[Project],project), project.actorName) }
  
  def receive = {
    case Initialize =>
      log.info("creating project actors")
      val projects = DB.withSession { implicit session: scala.slick.session.Session =>
        val q = for (project <- ProjectInfos) yield project.* 
        q.elements }
      projects.foreach { project => context.actorOf(Props(classOf[Project], project), project.actorName) }
    case CreateProject(user, name, description) =>
      DB.withSession { implicit session: Session =>
        val p = ProjectInfo(name = name, owner = user.name, description = description)
        val id = ProjectInfos.autoinc.insert(p)
        val project = p.copy(id = Some(id))
        context.actorOf(Props(classOf[Project], project), project.actorName)
        Seq(sender,context.parent).foreach(_ ! CreatedProject(p.copy(id = Some(id)))) }
    case DeleteProject(project) =>
      DB.withSession { implicit session: Session =>
        val q = for (p <- ProjectInfos if p.id === project.id) yield p      
        q.delete }
      context.actorSelection(project.actorName) ! PoisonPill
      Seq(sender,context.parent).foreach(_ ! DeletedProject(project))    
  }
  
  override def preStart() {
    self ! Initialize
  }
}