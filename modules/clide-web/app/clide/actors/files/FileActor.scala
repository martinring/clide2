package clide.actors.files

import clide.models.ProjectInfo
import akka.actor._
import clide.collaboration._
import clide.models._
import play.api.Play.current
import play.api.db.slick.DB
import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.Session
import java.io.File
import clide.actors._
import play.api.Play
import clide.collaboration._
import scala.collection.mutable.Buffer
import scala.util.Failure
import scala.util.Success
import play.api.libs.MimeTypes

class FileActor(project: ProjectInfo, parent: FileInfo, name: String) extends Actor 
                                                                         with ActorLogging
                                                                         with FileEventSource {
  import Messages._
  import Events._  
    
  var info: FileInfo = null  
  def file: File     = Play.getFile(project.root + info.path.mkString(File.pathSeparator))    
  
  var otActive = false
  var clients = Map[ActorRef,SessionInfo]()
  var server: Server = null
  
  def initOt() {
    val revs = DB.withSession { implicit session: Session => Revisions.get(info.id).toSeq }
    server = new Server(Document(""))
    log.info(f"reapplying ${revs.length} operations")
    for ((op,rev) <- revs.zipWithIndex) {
      server.applyOperation(op,rev) match {
        case Success(o) => // <- good          
        case Failure(e) => // <- bad ;)
          log.error(s"unable to apply revision $op (${e.getMessage}")
      } 
    }    
    otActive = true
  }
  
  def receiveMessages: Receive = {
    case WithPath(Seq(),any) => receiveMessages(any)
    
    case ExplorePath =>
      context.parent.forward(BrowseFolder)
      
    case OpenFile(user) =>
      if (!otActive) initOt()
      clients += sender -> user
      context.watch(sender)
      sender ! OTState(this.info, server.text, server.revision)
      
    case Annotate(rev,as) =>
      if (!otActive) initOt()
      server.transformAnnotation(rev.toInt, as) match { // TODO: Ugly: rev.toInt
        case Failure(e) =>
          // TODO
          log.warning("annotation could not be transformed")
        case Success(a) =>          
          clients.keys.filter(_ != sender).foreach(_ ! Annotated(info.id,clients(sender).id,a))
          sender ! AcknowledgeAnnotation
      }
      
    case Edit(rev,ops) =>
      if (!otActive) initOt()         
      server.applyOperation(ops,rev) match {
        case Failure(e) =>
          // TODO
          log.warning("edit couldnt be applied")
        case Success(o) =>
          DB.withSession { implicit session: Session => Revisions.insert(Revision(info.id,server.revision,o)) }
          clients.keys.filter(_ != sender).foreach(_ ! Edited(info.id, o))
          sender ! AcknowledgeEdit
      }      
      
    case TouchFile =>
      // Touched
      
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
            mimeType = MimeTypes.forFileName(name),
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