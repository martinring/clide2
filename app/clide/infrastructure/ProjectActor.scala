package clide.infrastructure

import akka.actor.Actor
import clide.models._
import akka.actor.ActorRef
import akka.actor.Props
import akka.actor.ActorLogging
import akka.actor.ActorPath

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
class ProjectActor(project: ProjectInfo) extends Actor with ActorLogging {
  import ProjectActor._
  
  def getFileActor(path: String) = {    
    val name = "file" + java.net.URLEncoder.encode(path,"UTF8")
    context.child(name).getOrElse(context.actorOf(Props(new FileActor(project,path)),name))
  }
  
  def getSessionActor(user: GenericUser) = {
    val name = "session" + java.net.URLEncoder.encode(user.name,"UTF8")
    context.child(name).getOrElse(context.actorOf(Props(new SessionActor(user,project))))
  }
  
  def receive = {
    case OpenSession(user) =>
      getSessionActor(user).forward(SessionActor.Register)         
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