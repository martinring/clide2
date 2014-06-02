/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
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
import akka.pattern.ask
import scala.concurrent.duration._
import akka.util.Timeout
import scala.util.Success

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
      val public = ProjectInfos.getPublic
      otherProjects = public.filter(_.owner != user.name).map(p => p -> ProjectAccessLevel.Write).toMap
      otherProjects ++= ProjectAccessLevels.getUserProjects(user.name).toMap.filter(_._1.owner != user.name) // TODO
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
    case External(user,login,msg) => (external(user,login) orElse anonymous)(msg)
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
      identified(backstagePeers(sender))(msg)
  }

  def anonymous: Receive = {
    case Login(password, isHuman) =>
      if (!user.authenticate(password)) {
        log.info("login attempt failed")
        sender ! WrongPassword
      } else {
        val key   = UUID.randomUUID().toString()
        val login = LoginInfo(user.name,key,None,isHuman) // TODO: Handle Timeouts!
        DB.withSession { implicit Session: Session => LoginInfos.create(login) }
        logins += key -> login
        sender ! LoggedIn(user, login)
        context.system.eventStream.publish(LoggedIn(user,login))
      }

    case _ => sender ! NotAllowed
  }

  def external(user: UserInfo, login: LoginInfo): Receive = {
    case WithProject(name,msg) =>
      projects.get(name) match {
        case Some(project) =>
          val access = DB.withSession { implicit session: Session =>
            ProjectAccessLevels.getProjectUsers(project.id).find(_._2 == user.name).map(_._3)
          }
          context.actorSelection(s"$name").tell(
            WrappedProjectMessage(user, login.isHuman, access.getOrElse(ProjectAccessLevel.None), msg),sender)
        case None => sender ! DoesntExist
      }

    case msg =>
      log.info("unauthorized external "+ msg.toString)
      sender ! NotAllowed
  }

  def identified(login: LoginInfo): Receive = {
    case Login(password, isHuman) =>
      if (!user.authenticate(password)) {
        log.info("login attempt failed")
        sender ! WrongPassword
      } else if (isHuman == login.isHuman) {
        sender ! LoggedIn(user, login)
      } else {
        log.warning("login key shared between human and non human users: {}", login)
        DB.withSession { implicit s: Session => LoginInfos.delete(login) }
      }

    case Logout =>
      DB.withSession { implicit sesion: Session => LoginInfos.delete(login) }
      logins -= login.key
      sender ! LoggedOut(user)
      context.system.eventStream.publish(LoggedOut(user))

    case CreateProject(name,description,public) =>
      if (name.toSeq.exists(a => !a.isLetterOrDigit && !(a == '-'))) {
        sender ! ProjectCouldNotBeCreated("The name must only consist of letters, digits and dashes")
      } else if (projects.contains(name)) {
        sender ! ProjectCouldNotBeCreated("A project with this name already exists")
      } else {
        val project = DB.withSession { implicit session: Session => ProjectInfos.create(name,user.name,description,public) }
        projects += name -> project
        context.actorOf(ProjectActor(project), project.name)
        sender ! CreatedProject(project)
        backstagePeers.keys.filter(_ != sender).foreach(_ ! CreatedProject(project))
      }

    case StartBackstageSession =>
      backstagePeers += sender -> login
      context.watch(sender)
      sender ! EventSocket(self,"backstage")

    case WithProject(name,msg) =>
      projects.get(name) match {
        case Some(project) =>
          context.actorSelection(s"$name").tell(
            WrappedProjectMessage(user, login.isHuman, ProjectAccessLevel.Admin, msg),sender)
        case None => sender ! DoesntExist
      }

    case WithUser(name,msg) =>
      if (name == user.name) (identified(login) orElse anonymous)(msg)
      else context.parent.forward(UserServer.Forward(name, External(user, login, msg)))

    case Validate => sender ! Validated(user)

    case BrowseProjects =>
      sender ! UserProjectInfos(projects.values.toSet,otherProjects.keySet)
  }
}
