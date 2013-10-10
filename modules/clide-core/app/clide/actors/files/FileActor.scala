package clide.actors.files

import akka.actor._
import clide.collaboration._
import clide.models._
import java.io.File
import clide.actors._
import scala.collection.mutable.Buffer
import scala.util.{Failure,Success}
import clide.Core.DB
import clide.Core.DAL._
import clide.Core.DAL.profile.simple._ // TODO: MOVE ALL TO SCHEMA

class FileActor(project: ProjectInfo, parent: FileInfo, name: String) extends Actor 
                                                                         with ActorLogging
                                                                         with FileEventSource {
  import Messages._
  import Events._  
    
  var info: FileInfo = null  
  def file = new File(project.root + info.path.mkString(File.pathSeparator)) // TODO    
  
  var otActive = false
  var clients = Map[ActorRef,SessionInfo]()
  var server: Server = null
  
  def initOt() {
    log.info("initializing ot")
    DB.withSession { implicit session: Session => 
      val revs = Revisions.get(info.id).toSeq
      server = new Server(Document(""))
      log.info(f"reapplying ${revs.length} operations")
      for ((op,rev) <- revs.zipWithIndex) {
        server.applyOperation(op,rev) match {
          case Success(o) => // <- good            
          case Failure(e) => // <- bad ;) TODO
            log.error(s"unable to apply revision $op (${e.getMessage}")
        }
      }
      log.info(server.text)
      otActive = true
    }    
  }
  
  def receiveMessages: Receive = {
    case WithPath(Seq(),any) => receiveMessages(any)
    
    case ExplorePath =>
      context.parent.forward(BrowseFolder)
      
    case OpenFile(user) =>
      log.info(s"opening for ${user.user}")
      if (!otActive) {
        try {
          initOt()
          clients += sender -> user
          context.watch(sender)
          sender ! OTState(this.info, server.text, server.revision)
        }
        catch {
          case e: Throwable =>
            log.error(e, "init failed")            
            sender ! FileInitFailed(this.info.id)
        }
      } else {
        clients += sender -> user
        context.watch(sender)
        sender ! OTState(this.info, server.text, server.revision)
      }
      
    case Annotate(_,rev,as,name) =>
      if (!otActive) initOt()      
      server.transformAnnotation(rev.toInt, as) match { // TODO: Ugly: rev.toInt
        case Failure(e) =>
          // TODO
          log.warning("annotation could not be transformed")
        case Success(a) =>
          log.info("annotated")
          clients.keys.filter(_ != sender).foreach(_ ! Annotated(info.id,clients(sender).id,a,name))
          sender ! AcknowledgeAnnotation
      }
      
    case Edit(_,rev,ops) =>
      if (!otActive) initOt()         
      server.applyOperation(ops,rev) match {
        case Failure(e) =>
          // TODO
          log.warning("edit couldnt be applied")
        case Success(o) =>
          log.info("edited")
          DB.withSession { implicit session: Session => Revisions.insert(Revision(info.id,server.revision,o)) }
          clients.keys.filter(_ != sender).foreach(_ ! Edited(info.id, o))
          sender ! AcknowledgeEdit
      }      
      
    case TouchFile =>
      log.info("touched")
      
    case Delete => // TODO !!      
      info = info.copy(deleted = true)
      val q = FileInfos.get(info.id)
      if (info.exists && !file.delete()) {                  
        DB.withSession { implicit session: Session => q.update(info) }
        file.deleteOnExit() // HACK: Schedule deletion instead
      } else {
        DB.withSession { implicit session: Session => q.delete }
      }
      triggerFileEvent(FileDeleted(info))      
      context.stop(self)
      
    case Terminated(ref) =>
      clients -= ref
  }
  
  def receive = receiveMessages orElse receiveFileEvents
  
  override def preRestart(reason:Throwable, message:Option[Any]){
    log.error(reason, "Unhandled exception for message: {}", message)
  }
  
  override def preStart() {
    initFileEventSource()
    val q = FileInfos.get(project, parent.path :+ name) 
    DB.withSession { implicit session: Session =>
      q.firstOption match {
        case None => // The file did not previously exist
          info = FileInfos.create(
            project = project.id,
            path    = parent.path :+ name,
            mimeType = Some("text/x-isabelle"), // TODO:  MimeTypes.forFileName(name),
            deleted = false,
            exists  = false,
            isDirectory = false,
            parent = Some(parent.id)
          )
          log.info("file created: " + info)
          triggerFileEvent(FileCreated(info))
        case Some(info) =>
          if (info.deleted) { // The file was in a deleted state
            this.info = info.copy(deleted = false)
            q.update(this.info)
            log.info("file created: " + info)
            triggerFileEvent(FileCreated(this.info))
          } else {
            this.info = info
          }
      }
    } 
  }
}