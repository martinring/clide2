package clide.plugins

import akka.actor._
import com.typesafe.config.ConfigFactory
import scala.concurrent.duration._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models._
import isabelle.Thy_Load
import clide.collaboration.Document
import isabelle.Session
import isabelle.Outer_Syntax
import clide.collaboration.Annotate
import clide.collaboration.Plain
import clide.collaboration.Annotations
import clide.collaboration.Annotation

object Isabelle extends App {  
  val system = ActorSystem("clide-isabelle",ConfigFactory.load.getConfig("clide-isabelle")) 
  implicit val dispatcher = system.dispatcher
  
  system.actorOf(Props[Isabelle],"plugin") 
}

class Isabelle extends Actor with ActorLogging {
  implicit val dispatcher = context.dispatcher
  
  val config = context.system.settings.config
  
  val username = config.getString("plugin.username")
  val email    = config.getString("plugin.email")
  val password = config.getString("plugin.password")    
  
  var server   = context.system.deadLetters
  var peer     = context.system.deadLetters
  var sessions = Set[ActorRef]() 
  
  def login() = {
    log.info("attempting login")
    server ! AnonymousFor(username,Login(password))
  }
  
  def signup() = {
    log.info(s"signing up $username")
    server ! SignUp(username,email,password)
  }
  
  def loggedIn(login: LoginInfo): Receive = {    
    case LoggedOut(user) =>
      log.info("logged out")
      context.system.shutdown()
    case EventSocket(peer,"backstage") =>
      log.info("connected to backstage session")
      this.peer = peer
      log.info("requesting project infos")
      peer ! BrowseProjects
    case UserProjectInfos(own,other) =>
      log.info("received project infos")
      (own ++ other).foreach { project =>
        log.info(s"starting session for ${project.owner}/${project.name}")
        val act = context.actorOf(Props(classOf[IsabelleProjectSession],project,login,server),s"p${project.id}")
        sessions += act
        context.watch(act)
      }
  }
  
  def receive = {
    case ActorIdentity("server",None) =>
      log.error("couldn't reach the server")
      context.system.shutdown()
    case ActorIdentity("server",Some(ref)) =>
      server = ref
      log.info("connected to clide")
      login()
    case DoesntExist =>
      log.info(s"user $username hasnt been signed up yet")      
      signup()
    case WrongPassword =>
      log.error(s"user $username is already signed up with different password")
      context.system.shutdown()
    case SignedUp(info) =>
      log.info(s"signed up")
      login()
    case LoggedIn(info, login) => // TODO: UserInfo contains password hash!!!
      log.info(s"logged in")
      server ! IdentifiedFor(username,login.key,StartBackstageSession)
      context.become(loggedIn(login))
  }
  
  override def preStart() = {
    log.info("initializing isabelle plugin")
    isabelle.Isabelle_System.init()
    val path   = context.system.settings.config.getString("plugin.server-path")
    val server = context.actorSelection(path)
    server ! Identify("server")
  }
}

class IsabelleProjectSession(project: ProjectInfo, login: LoginInfo, server: ActorRef) extends Actor with ActorLogging {    
  var session = context.system.deadLetters
  var activeFiles = Map[Long,Long]()
  var info: SessionInfo = null
  var collaborators = Set[SessionInfo]()
  var files = Map[Long,OpenedFile]()
  
  val is = new isabelle.Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty))
  
  def receive = {    
    case EventSocket(ref,"session") =>
      log.info("session started")
      session = ref
      log.info("requesting session info")
      session ! RequestSessionInfo
    case SessionInit(info, collaborators) =>
      log.info("session info received")
      this.info = info
      this.collaborators = collaborators
      collaborators.foreach { info =>
        if (info.active && info.activeFile.isDefined) {
          log.info(s"${info.user} is looking at ${info.activeFile.get}")
          activeFiles += info.id -> info.activeFile.get          
        }
      }
      activeFiles.values.toSeq.distinct.foreach { id =>
        session ! SwitchFile(id)
      }
    case FileOpened(file@OpenedFile(info,content,revision)) =>
      val as = Annotations(is.thy_load.base_syntax.scan(content).map { case t: isabelle.Token =>
        (if (t.is_command) {
          Annotate(t.content.length(),Map("c"->"cm-keyword"))	       
	    } else if (t.is_comment) {
	      Annotate(t.content.length(),Map("c"->"cm-comment"))
	    } else if (t.is_string) {
	      Annotate(t.content.length(),Map("c"->"cm-string"))          
        } else Plain(t.content.length())): Annotation
      })
      session ! clide.actors.Messages.Annotate(revision,as)
      log.info(file.toString)
      files += info.id -> file
    case Edited(file,operation) => try {
      log.info(file.toString + ": " + operation)
      files.get(file).map { case OpenedFile(info,content,revision) =>
        val next = OpenedFile(info,new Document(content).apply(operation).get.content,revision + 1)
        log.info(next.toString)
        val as = Annotations(is.thy_load.base_syntax.scan(next.state).map { case t: isabelle.Token =>
	      (if (t.is_command) {
	        Annotate(t.content.length(),Map("c"->"cm-keyword"))	       
	      } else if (t.is_comment) {
	        Annotate(t.content.length(),Map("c"->"cm-comment"))
	      } else if (t.is_string) {
	        Annotate(t.content.length(),Map("c"->"cm-string"))
	      } else Plain(t.content.length())): Annotation
	    })
	    session ! clide.actors.Messages.Annotate(next.revision,as)
        files += file -> next
      }
    } catch { case e: Throwable => log.error(e.getMessage()) }
    case SessionChanged(info) =>
      if (info.active && info.activeFile.isDefined) {
        log.info(s"${info.user} is looking at ${info.activeFile.get}")        
        activeFiles += info.id -> info.activeFile.get        
        session ! SwitchFile(info.activeFile.get)
      } else {
        log.info(s"${info.user} is inactive")
        activeFiles -= info.id
      }
  }
  
  override def preStart() {
    log.info("initializing project")    
    server ! IdentifiedFor(login.user,login.key,WithUser(project.owner,WithProject(project.name,StartSession)))
  }
}