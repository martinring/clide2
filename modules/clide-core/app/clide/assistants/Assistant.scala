 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 \*                                                                           */

package clide.assistants

import com.typesafe.config.Config
import akka.actor._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models._
import clide.actors.util.ServerForwarder

/**
 * This is a convenience class to implement connected tools. (Assistants)
 * The only method to be implemented is the `createSession` message, which should
 * create an instance of an Actor which may inherit from 
 * [[clide.assistants.AssistantSession `AssistantSession`]]
 * 
 * @author Martin Ring
 */
abstract class Assistant extends Actor with ActorLogging {
  /**
   * Must be implemented by subclasses to create instances of session actors for
   * a specific project.
   * 
   * @param   project the project to create a session for
   * @returns the reference to the created session actor.
   */
  def createSession(project: ProjectInfo): ActorRef   
  
  /** May be overridden to modify invitation behaviour **/
  def onInvitation(project: ProjectInfo, me: LoginInfo) = {
    log.info(s"starting session for ${project.owner}/${project.name}")
    val act = createSession(project)
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
          sessions.get(project.id).map(_ ! AssistantSession.Close)
      case CreatedProject(project) =>
        onInvitation(project,loginInfo)
      case DeletedProject(project) =>        
        sessions.get(project.id).map(_ ! AssistantSession.Close)
      case Terminated(sess) =>        
        sessions.find(_._2 == sess).foreach(i => sessions.remove(i._1))
    }
  }
}