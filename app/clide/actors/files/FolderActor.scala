package clide.actors.files

import akka.actor.Actor
import akka.actor.Props
import clide.models.ProjectInfo
import play.api.Play
import play.api.Play.current
import java.io.File
import akka.actor.ActorLogging
import clide.models._
import play.api.db.slick.DB
import scala.slick.driver.H2Driver.simple._
import play.api.db.slick.Session
import clide.actors._

/** Watches and manages a Folder **/
class FolderActor(project: ProjectInfo, parent: Option[FileInfo], name: String) extends Actor 
                                                                           with ActorLogging 
                                                                           with FileEventSource {
  import Messages._
  import Events._
      
  val fullPath = parent.map(_.path).getOrElse("") + File.pathSeparator + name
  
  var info:     FileInfo      = null  
  var children: Map[Long,FileInfo] = Map()
  def file:     File          = Play.getFile(project.root + info.path.mkString(File.pathSeparator))     
  
  def getFolder(name: String) = context.child(name).getOrElse{
    context.actorOf(Props(classOf[FolderActor], project, Some(info), name),name) }
  
  def getFile(name: String) = context.child(name).getOrElse{
    context.actorOf(Props(classOf[FileActor], project, info, name),name) }
  
  def getExisting(name: String) = context.child(name).orElse {
    children.values.find(_.path.last == name).map { i =>
      if (i.isDirectory) getFolder(name)
      else getFile(name) }
  } 
  
  def receiveMessages: Receive = {
    case e @ FileCreated(file) =>
      triggerFileEvent(e)
      if (file.parent.map(_ == info.id).getOrElse(false)) {
        log.info("adding to children")
        children += file.id -> file
      }
    case e @ FileDeleted(file) =>
      triggerFileEvent(e)
      if (file.parent.map(_ == info.id).getOrElse(false)) {
        log.info("removing child")
        children -= file.id
      }
    case WithPath(Seq(), msg) => receiveMessages(msg)            
    case WithPath(Seq(name), Delete) => 
      getExisting(name).map(_.forward(Delete))      
    case WithPath(Seq(name), OpenFile) =>
      getFile(name).forward(OpenFile)
    case WithPath(Seq(name), TouchFile) =>
      getFile(name).forward(TouchFile)
    case WithPath(Seq(name), msg@Edit(_,_,_)) =>
      log.info("forward")
      getFile(name).forward(msg)
    case WithPath(Seq(name,tail@_*), ExplorePath) =>
      getExisting(name).fold{        
        receiveMessages(BrowseFolder)  
      }( _.forward(WithPath(tail,ExplorePath) ))
    case WithPath(Seq(head,tail@_*), msg) =>
      getFolder(head).forward(WithPath(tail, msg))
      
    case NewFile =>
      def findName(n: Int = 1): String = {
        val name = if (n > 1) "unnamed" + n else "unnamed"
        if (children.values.exists(_.path.last == name))
          findName(n+1)
        else name
      }
      val name = findName()
      log.info(s"creating new file: $name")
      getFile(findName()) ! NewFile
    case ExplorePath => receiveMessages(BrowseFolder)    
	case BrowseFolder =>
	  log.info(children.toString)
      sender ! FolderContent(info,children.values.toSeq)
	case TouchFolder =>
	  // Touched
    case Delete =>
      context.children.foreach { child =>
        // We unregister from our children's events in order to
        // get just one event triggered for the deletion of this
        // folder       
        child ! Unregister
        // Now we can propagate the deletion to all of our children
        // which still means, that their event listeners receive
        // a delete event.
        context.children.foreach(_ ! Delete)
      }
      // In many cases we will not be able to delete the file on
      // the disk right now. For those cases we have to mark the
      // file as deleted and postpone the deletion. Otherwise we
      // can remove all evidences right away.
      info = info.copy(deleted = true)
      val q = FileInfos.get(info.id)
      if (!file.delete()) {                  
        DB.withSession { implicit session: Session => q.update(info) }
        file.deleteOnExit() // HACK: Schedule deletion instead
      } else {          
        DB.withSession { implicit session: Session => q.delete }
      }
      triggerFileEvent(FileDeleted(info))
      context.stop(self)
  }
  
  def receive = receiveMessages orElse receiveFileEvents
  
  override def preStart = {
    initFileEventSource()
    val q = FileInfos.get(project, parent.map(_.path :+ name).getOrElse(Seq.empty)) 
    DB.withSession { implicit session: Session =>
      q.firstOption match {
        case None => // The file did not previously exist
          info = FileInfos.create(
            project = project.id,
            path    = parent.map(_.path :+ name).getOrElse(Seq.empty),
            mimeType = None,
            deleted = false,
            exists  = false,
            isDirectory = true,
            parent = parent.map(_.id)
          )
          log.info("created file " + info)
          triggerFileEvent(FileCreated(info))
        case Some(info) =>  
          if (info.deleted) { // The file was in a deleted state
            this.info = info.copy(deleted = false)
            q.update(this.info)
            log.info("created file " + info)
            triggerFileEvent(FileCreated(info))
          } else {
            this.info = info
          }          
          this.children = FileInfos.getChildren(info.id).elements().map(i => i.id -> i).toMap
          log.info(this.children.toString)
      }
    } 
  }
}