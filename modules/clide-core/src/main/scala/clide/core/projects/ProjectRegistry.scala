/*package clide.core.projects

import akka.persistence.EventsourcedProcessor
import scala.collection.mutable.Map
import akka.actor._
import clide.core.users.UserActor
import clide.core.users.Auth

object ProjectRegistry {
  def props(user: String) = Props(classOf[ProjectRegistry], user)

  case class Created(info: ProjectInfo)
}

class ProjectRegistry(user: String) extends EventsourcedProcessor with ActorLogging {
  val projects = Map.empty[String,ActorRef]

  def receiveRecover = {
    case msg @ ProjectRegistry.Created(info) =>
      //projects += (info.owner, info.name) -> context.actorOf(ProjectActor.props(info), info.owner + "$" + info.name)
  }

  def receiveCommand = {
    case UserActor.AuthorizedRequest(user, id, Project.Create(name,public))  =>
      if (user != this.user)
        sender ! Auth.Response(id,Auth.AuthenticationRefused)
      if (!name.matches("[a-zA-Z0-9_-\\.]+"))
        sender ! Auth.Response(id,Project.CreationRefused(Project.CreationRefused.InvalidName))
      else if (projects.isDefinedAt(name))
        sender ! Auth.Response(id,Project.CreationRefused(Project.CreationRefused.NameNotUnique))
      else {
        persist(ProjectRegistry.Created(ProjectInfo(user,name,public))) { msg =>

        }
      }
  }
}*/
