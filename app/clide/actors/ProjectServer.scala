package clide.actors

import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import akka.actor._
import java.net.URLEncoder
import clide.models._
import akka.actor.PoisonPill
import scala.slick.session.Session
import clide.actors.projects._

class ProjectServer extends Actor with ActorLogging {
  import Messages._
  import Events._
  import projects._
  
  def getProjectActor(id: Long): ActorRef = context.child(id.toString()).getOrElse {
    context.actorOf(Props(classOf[ProjectActor],id),id.toString) }
 
  def receive = {      
    case CreateProject(user,name,description) =>
      var project = ProjectInfo(None, name = name, owner = user.name, description = description)
      val id = DB.withSession { implicit session: Session => ProjectInfos.autoinc.insert(project) }
      project = project.copy(id = Some(id))
      context.actorOf(Props(classOf[ProjectActor], project), project.id.toString())
      sender         ! CreatedProject(project)
      context.parent ! CreatedProject(project)
      
    case WithProject(project,message: FileMessage) =>      
      getProjectActor(project).forward(message)
  }
  
  override def preStart() {    
    log.info("creating project actors")
    val q = for (project <- ProjectInfos) yield project.*
    val projects = DB.withSession { implicit session: scala.slick.session.Session => q.elements }
    projects.foreach { project => context.actorOf(Props(classOf[ProjectActor], project), project.id.toString()) }
  }
}