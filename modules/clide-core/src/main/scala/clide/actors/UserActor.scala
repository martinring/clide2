/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */
package clide.actors

import akka.actor._
import clide.models._
import scala.slick.session.Session
import java.util.UUID
import clide.persistence.DBAccess

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private object UserActor {
  def props(user: UserInfo with Password)(implicit dbAccess: DBAccess) =
    Props(classOf[UserActor], user, dbAccess)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class UserActor(var user: UserInfo with Password)(implicit val dbAccess: DBAccess) extends Actor with ActorLogging {
  println("instance created")
  import dbAccess.schema._
  import dbAccess.{db => DB}
  import Messages.internal._
  import Messages._
  import Events._

  var logins = Map[String,LoginInfo]()
  var projects = Map[String,ProjectInfo]()
  var otherProjects = Map[ProjectInfo,ProjectAccessLevel.Value]()
  var backstagePeers: Map[ActorRef,LoginInfo] = Map()

  override def preStart() {
    log.info("initializing user actor")
    DB.withSession { implicit session: Session =>
      logins = LoginInfos.getByUser(user.name).map(l => l.key -> l).toMap
      projects = ProjectInfos.getByOwner(user.name).map(p => p.name -> p).toMap // TODO
      otherProjects = ProjectAccessLevels.getUserProjects(user.name).toMap.filter(_._1.owner != user.name) // TODO
    }
    for (project <- otherProjects.keys)
      log.info(s"${user.name} collaborates in ${project.name} of ${project.owner}")
    log.info("creating project actors")
    projects.foreach { case (name,project) =>
      context.actorOf(ProjectActor(project),name)
    }
  }

  def authenticate(key: String): Either[AuthEvent,LoginInfo] =
    logins.get(key).toRight(SessionTimedOut) // TODO: Handle Timeouts

  def receive = {
    case Identified(key,msg) => authenticate(key).fold(
        { event => sender ! event },
        { login => (identified(login) orElse anonymous)(msg) })
    case Anonymous(msg) => anonymous(msg)
    case External(user,msg) => (external(user) orElse anonymous)(msg)
    // EVENTS
    case DeletedProject(project) =>
      projects -= project.name
      backstagePeers.keys.foreach(_ ! DeletedProject(project))
    case Terminated(peer) =>
      backstagePeers -= peer
    case msg@ChangedProjectUserLevel(project, user, level) =>
      if (user == this.user.name) {
        otherProjects += project -> level
        backstagePeers.keys.foreach(_ ! msg)
      } else {
        context.actorSelection(s"../$user").tell(msg,sender)
      }
    case msg if backstagePeers.contains(sender) && identified(backstagePeers(sender)).isDefinedAt(msg) => // TODO: Move to dedicated backstage actor
      log.info("direct message via backstage: {}",msg)
      identified(backstagePeers(sender))(msg)
  }

  def anonymous: Receive = {
    case Login(password) =>
      if (!user.authenticate(password)) {
        log.info("login attempt failed")
        sender ! WrongPassword
      } else {
        val key   = UUID.randomUUID().toString()
        val login = LoginInfo(user.name,key,None) // TODO: Handle Timeouts!
        DB.withSession { implicit Session: Session => LoginInfos.create(login) }
        logins += key -> login
        sender ! LoggedIn(user, login)
        context.system.eventStream.publish(LoggedIn(user,login))
      }

    case _ => sender ! NotAllowed
  }

  def external(user: UserInfo): Receive = {
    case WithProject(name,msg) =>
      projects.get(name) match {
        case Some(project) =>
          context.actorSelection(s"$name").tell(
            WrappedProjectMessage(user, ProjectAccessLevel.Write,msg),sender)
        case None => sender ! DoesntExist
      }

    case msg =>
      log.info("external "+ msg.toString)
      sender ! NotAllowed
  }

  def identified(login: LoginInfo): Receive = {
    case Login(password) =>
      if (!user.authenticate(password)) {
        log.info("login attempt failed")
        sender ! WrongPassword
      } else
        sender ! LoggedIn(user, login)

    case Logout =>
      DB.withSession { implicit sesion: Session => LoginInfos.delete(login) }
      logins -= login.key
      sender ! LoggedOut(user)
      context.system.eventStream.publish(LoggedOut(user))

    case CreateProject(name,description) =>
      if (name.toSeq.exists(!_.isLetterOrDigit)) {
        sender ! ProjectCouldNotBeCreated("The name must only consist of letters and digits")
      } else if (projects.contains(name)) {
        sender ! ProjectCouldNotBeCreated("A project with this name already exists")
      } else {
        val project = DB.withSession { implicit session: Session => ProjectInfos.create(name,user.name,description) }
        projects += name -> project
        context.actorOf(ProjectActor(project), project.name)
        sender ! CreatedProject(project)
        backstagePeers.keys.foreach(_ ! CreatedProject(project))
      }

    case StartBackstageSession =>
      backstagePeers += sender -> login
      context.watch(sender)
      sender ! EventSocket(self,"backstage")

    case WithProject(name,msg) =>
      projects.get(name) match {
        case Some(project) =>
          context.actorSelection(s"$name").tell(
            WrappedProjectMessage(user, ProjectAccessLevel.Admin,msg),sender)
        case None => sender ! DoesntExist
      }

    case WithUser(name,msg) =>
      log.info(s"${user.name} received $msg for $name")
      if (name == user.name) (identified(login) orElse anonymous)(msg)
      else context.actorSelection(s"../$name").tell(External(user,msg),sender)

    case Validate => sender ! Validated(user)

    case BrowseProjects =>
      sender ! UserProjectInfos(projects.values.toSet,otherProjects.keySet)
  }
}
