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
import clide.actors.projects._

object ProjectServer {
  trait Message
  case object Initialize extends Message
  case class CreateProject(user: UserInfo, name: String, description: Option[String] = None) extends Message
  case class WithProject(owner: String, name: String, message: ProjectActor.Message) extends Message
  
  trait ProjectEvent
  case class CreatedProject(project: ProjectInfo) extends ProjectEvent
  case class DeletedProject(project: ProjectInfo) extends ProjectEvent
}

class ProjectServer extends Actor with ActorLogging {
  import ProjectServer._
  import projects._
  
  def getProject(project: ProjectInfo) = context.child(project.actorName).getOrElse {
    context.actorOf(Props(classOf[ProjectActor],project), project.actorName) }
  
  def receive = {
    case Initialize =>
      log.info("creating project actors")
      val q = for (project <- ProjectInfos) yield project.*
      val projects = DB.withSession { implicit session: scala.slick.session.Session => q.elements }
      projects.foreach { project => context.actorOf(Props(classOf[ProjectActor], project), project.actorName) }
      
    case CreateProject(user,name,description) =>
      var project = ProjectInfo(None, name = name, owner = user.name, description = description)
      val id = DB.withSession { implicit session: Session => ProjectInfos.autoinc.insert(project) }
      project = project.copy(id = Some(id))
      context.actorOf(Props(classOf[ProjectActor], project), project.actorName)
      sender         ! CreatedProject(project)
      context.parent ! CreatedProject(project)
      
    case WithProject(owner,name,message) =>
      getProject(ProjectInfo(None,name=name,owner=owner,description=None)).forward(message)
  }
  
  override def preStart() {
    self ! Initialize
  }
}