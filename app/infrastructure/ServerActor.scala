package infrastructure

import akka.actor.Actor
import models.GenericUser
import akka.actor.ActorRef
import models.Project
import akka.actor.ActorLogging
import play.api.Logger
import scala.collection.mutable.Map

/** 
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ServerActor extends Actor with ActorLogging {
  import ServerActor._
  
  val projects = Map[Long,ActorRef]()
  
  def createProjectActor(project: Project): ActorRef = {
    null
  }
  
  def receive = {
    case OpenSession(user,project) =>
      log.info(f"user '${user.name}' requested a session for project '${project.name}'")     
      //projects.getOrElseUpdate(project., op)
      val selection = context.actorSelection(project.uniqueName)
      
      SessionOpened(self)
  }
  
  override def preStart() {    
    log.info("infrastructure server started")
  }
}

object ServerActor {
  trait ServerRequest
  case class OpenSession(user: GenericUser, project: Project) extends ServerRequest  
  
  trait ServerReply
  case class SessionOpened(session: ActorRef) extends ServerReply    
}