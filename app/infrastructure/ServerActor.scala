package infrastructure

import scala.collection.mutable.Map
import akka.actor.Actor
import akka.actor.ActorLogging
import akka.actor.ActorRef
import akka.actor.Props
import models.GenericUser
import models.Project

/** 
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ServerActor extends Actor with ActorLogging {
  import Messages._
  val projectActors = Map[Long,ActorRef]()
  
  def createProjectActor(project: Project): ActorRef = {
    projectActors(project.id.get) = context.actorOf(Props(new ProjectActor(project)),project.id.get.toString)
    projectActors(project.id.get)
  }
  
  def receive = {
    case OpenSession(user,project) =>      
      log.info(f"user '${user.name}' requested a session for project '${project.name}'")      
      val pa = projectActors.get(project.id.get) match {
        case None => createProjectActor(project)
        case Some(ref) if (ref.isTerminated) => createProjectActor(project)
        case Some(ref) => ref
      }
      pa.forward(OpenSession(user,project))
  }
  
  override def preStart() {    
    log.info("infrastructure server started")
  }
}