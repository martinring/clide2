package infrastructure

import akka.actor.Actor
import models._
import akka.actor.ActorRef
import akka.actor.Props
import akka.actor.ActorLogging
import akka.actor.ActorPath

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ProjectActor(project: Project) extends Actor with ActorLogging {
  import ProjectActor._
  
  def getFileActor(path: String) = {    
    val name = java.net.URLEncoder.encode(path)
    context.child(name).getOrElse(context.actorOf(Props(new FileActor(project,path)),name))        
  }
  
  def receive = {
    case OpenSession(user) =>
      sender ! ServerActor.Welcome(context.actorOf(Props(new SessionActor(user,project))).path)    
    case WithFile(path,request) =>
      getFileActor(path).forward(request)
  }
  
  override def preStart {
    log.info("project actor started")
  }
}

object ProjectActor {
  trait Request
  case class OpenSession(user: GenericUser) extends Request
  case class WithFile(path: String, request: FileActor.Request)  
  
  trait Reply  
  case class FileOpened(path: ActorPath)
}