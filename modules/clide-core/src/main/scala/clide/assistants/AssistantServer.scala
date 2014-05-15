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

package clide.assistants

import com.typesafe.config.Config
import akka.actor._
import akka.actor.OneForOneStrategy._
import akka.actor.SupervisorStrategy._
import scala.concurrent.duration._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models._
import clide.actors.util.ServerForwarder
import com.typesafe.config.ConfigFactory
import akka.kernel.Bootable
import scala.reflect.ClassTag
import scala.concurrent.Future

import clide.collaboration.Operation

/**
 * An assistant server is the entry point for the implementation of an assistant.
 * It requires a constructor for an AssistantBehavior which takes an AssistantControl
 * as an Argument. The constructor will be called, when a new Assistant Session for a
 * project is created. The name, server and credentials for the assistant must be configured
 * in an application.conf file. (see reference.conf for example values)
 *
 * @author Martin Ring <martin.ring@dfki.de>
 */
class AssistantServer(behavior: AssistantControl => AssistBehavior)(implicit dummy: DummyImplicit) extends Bootable {    
  val system = ActorSystem("assistant",ConfigFactory.load)

  val config = system.settings.config

  def startup() {
    system.actorOf(Props(classOf[AssistantServerActor], (p: ProjectInfo) => Props(classOf[Assistant], p, behavior)), config.getString("assistant.username"))
  }

  def shutdown() {
    system.shutdown()
  }
  
  /*override val supervisorStrategy = OneForOneStrategy(maxNrOfRetries = 10, withinTimeRange = 5 seconds) {
    case _: 
  }*/
  
  // should be deprecated some time in the future, when assistbehavior becomes stable
  //@deprecated("Use Future-based AssistBehavior instead!","2.0-SNAPSHOT")
  def this(behavior: AssistantControl => AssistantBehavior) = this {(control: AssistantControl) =>
    val underlying = behavior(control)
    import control.executionContext
    new AssistBehavior {
      def start(project: ProjectInfo): Future[Unit] = Future(underlying.start(project))
		  def stop: Future[Unit] = Future(underlying.stop)
		  def mimeTypes: Set[String] = underlying.mimeTypes
		  def fileOpened(file: OpenedFile): Future[Unit] = Future(underlying.fileOpened(file))
		  def fileActivated(file: OpenedFile): Future[Unit] = Future(underlying.fileActivated(file))
		  def fileInactivated(file: OpenedFile): Future[Unit] = Future(underlying.fileInactivated(file))
		  def fileClosed(file: OpenedFile): Future[Unit] = Future(underlying.fileClosed(file))
		  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]): Future[Unit] = Future(underlying.fileChanged(file, delta, cursors))
		  def collaboratorJoined(who: SessionInfo): Future[Unit] = Future(underlying.collaboratorJoined(who))
  	  def collaboratorLeft(who: SessionInfo): Future[Unit] = Future(underlying.collaboratorLeft(who))
  	  def cursorMoved(cursor: Cursor): Future[Unit] = Future(underlying.cursorMoved(cursor))
      def annotationsRequested(file: OpenedFile, name: String): Future[Unit] = Future(underlying.annotationsRequested(file, name))
      def annotationsDisregarded(file: OpenedFile, name: String): Future[Unit] = Future(underlying.annotationsDisregarded(file, name))
      def receiveChatMessage(from: SessionInfo, msg: String, tpe: Option[String], timestamp: Long): Future[Unit] = Future(underlying.receiveChatMessage(from.user, msg, tpe, timestamp))
      def helpRequest(from: SessionInfo, file: OpenedFile, pos: Int, id: String, request: String): Future[Unit] = noop
    }
  }
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private class AssistantServerActor(sessionProps: ProjectInfo => Props) extends Actor with ActorLogging {
  var actors = Map.empty[ActorRef,(ProjectInfo,LoginInfo)]
  
  /** May be overridden to modify invitation behaviour **/
  def onInvitation(project: ProjectInfo, me: LoginInfo) = {
    log.info(s"starting session for ${project.owner}/${project.name}")
    val act = context.actorOf(sessionProps(project))
    actors += act -> (project,me)    
    server.tell(IdentifiedFor(me.user,me.key,WithUser(project.owner,WithProject(project.name,StartSession))),act)
    context.watch(act)
  }

  lazy val config     = context.system.settings.config

  lazy val username   = config.getString("assistant.username")
  lazy val password   = config.getString("assistant.password")
  lazy val email      = config.getString("assistant.email")

  lazy val serverPath = config.getString("assistant.server-path")
  lazy val server     = context.actorOf(ServerForwarder(serverPath), "server-forwarder")

  private def login() = {
    log.info("attempting login")
    server ! AnonymousFor(username,Login(password))
  }

  private def signup() = {
    log.info(s"signing up $username")
    server ! SignUp(username,email,password)
  }

  def receive = loggedOut

  private def loggedOut: Receive = {
    login()

    {
      case DoesntExist =>
        log.info(s"user $username hasnt been signed up yet")
        signup()
      case WrongPassword =>
        log.error(s"user $username is already signed up with different password")
        self ! PoisonPill
      case SignedUp(info) =>
        log.info(s"signed up")
        login()
      case LoggedIn(info, login) => // TODO: UserInfo contains password hash!!!
        context.become(loggedIn(login))
    }
  }

  private def loggedIn(loginInfo: LoginInfo): Receive = {
    log.info(s"logged in")
    server ! IdentifiedFor(username,loginInfo.key,StartBackstageSession)

    {
      case LoggedOut(user) =>
        context.become(loggedOut)
        log.info("logged out")
        self ! PoisonPill
      case EventSocket(peer,"backstage") =>
        log.info("connected to backstage session")
        log.info("requesting project infos")
        context.become(backstage(loginInfo,peer))
        peer ! BrowseProjects
    }
  }

  private def backstage(loginInfo: LoginInfo, peer: ActorRef): Receive = {
    val sessions = scala.collection.mutable.Map.empty[Long,ActorRef]

    {
      case UserProjectInfos(own,other) =>
        log.info("received project infos")
        (own ++ other).foreach(onInvitation(_,loginInfo))
      case ChangedProjectUserLevel(project, user, level) if (user == loginInfo.user) =>
        if (level >= ProjectAccessLevel.Read)
          onInvitation(project, loginInfo)
        else          
          sessions.get(project.id).map(_ ! PoisonPill)
          sessions.remove(project.id)
      case CreatedProject(project) =>
        onInvitation(project,loginInfo)
      case DeletedProject(project) =>
        sessions.get(project.id).map(_ ! PoisonPill)
      case ServerForwarder.Restarted =>
        throw new Exception("the server was restarted")
      case Terminated(sess) =>        
        sessions.find(_._2 == sess).foreach { case (id,act) =>
          actors.get(sess).foreach { case (p,i) =>
            log.info("restarting project actor")
            onInvitation(p,i)
          }
        }
    }
  }
  
  override def preStart {
    server ! ServerForwarder.Subscribe
  }
  
  override def postStop {
    server ! ServerForwarder.Unsubscribe
  }
}
