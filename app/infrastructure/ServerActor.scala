package infrastructure

import scala.collection.mutable.Map
import akka.actor.Actor
import akka.actor.ActorLogging
import akka.actor.ActorRef
import akka.actor.Props
import models.GenericUser
import models.ProjectInfo
import akka.actor.ActorPath

/** 
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ServerActor extends Actor with ActorLogging {
  import ServerActor._  
      
  def getProjectActor(project: ProjectInfo): ActorRef = {
    val name = java.net.URLEncoder.encode(project.uniqueName,"UTF8")
    context.child(name).getOrElse(context.actorOf(Props(new ProjectActor(project)),name))
  }  
  
  def receive = {
    case OpenSession(user,project) =>
      log.info(f"user '${user.name}' requested a session for project '${project.name}'")
      getProjectActor(project).forward(ProjectActor.OpenSession(user))
  }
  
  override def preStart() {    
    log.info("infrastructure server started")
  }
}

object ServerActor {
  trait Request
  case class OpenSession(user: GenericUser, project: ProjectInfo)
  
  trait Reply
  case class  WelcomeToSession(session: ActorRef)
  case object SessionAlreadyInUse
}