package clide.actors

import scala.slick.driver.H2Driver.simple._
import akka.actor.Actor
import play.api.Play.current
import play.api.db.slick.DB
import akka.actor.Props
import akka.actor.ActorLogging
import clide.models.ProjectInfo

object Projects {
  trait Message
  case object Initialize extends Message
  case class Created(project: ProjectInfo) extends Message
  case class Deleted(project: ProjectInfo) extends Message
}

class Projects extends Actor with ActorLogging {
  import Projects._
  import projects._
  
  def receive = {
    case Initialize =>
      log.info("creating project actors")
      val projects = DB.withSession { implicit session: scala.slick.session.Session =>
        val q = for (project <- clide.models.Projects) yield project.* 
        q.elements }
      projects.foreach { project => context.actorOf(Props(classOf[Project], project), project.uniqueName) }
    case Created(project) =>
      context.actorOf(Props(classOf[Project],project),project.uniqueName)
  }
  
  override def preStart() {
    self ! Initialize
  }
}