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
package clide.actors.files

import akka.actor._
import clide.collaboration._
import clide.models._
import java.io.File
import clide.actors._
import scala.collection.mutable.{Buffer,Map}
import scala.util.{Try,Failure,Success}

private[actors] object FileActor {
  def props(project: ProjectInfo, parent: FileInfo, name: String) =
    Props(classOf[FileActor], project, parent, name)
}

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
private[actors] class FileActor(project: ProjectInfo, parent: FileInfo, name: String) extends Actor
                                                                         with ActorLogging
                                                                         with FileEventSource {
  import clide.Core.{ db => DB }
  import clide.Core.schema._
  import clide.Core.profile.simple._  
  import Messages._
  import Events._

  var info: FileInfo = null
  def file = new File(project.root + info.path.mkString(File.pathSeparator)) // TODO

  var otActive = false
  val clients = Map[ActorRef,SessionInfo]()
  var server: Server[Char] = null

  val annotations = Map[(Long,String),(Long,Annotations)]()
  val subscriptions = Map[(Long,String),Set[ActorRef]]()
  val descriptions = Map[(Long,String),String]()
  
  val mimeTypes = context.system.settings.config.getConfig("mimeTypes") 

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
      log.info("done")
      otActive = true
    }
  }

  def resendAnnotations(receiver: ActorRef) = {
    annotations.foreach {
      case ((u,n),(r,a)) =>
        val before = subscriptions.get((u,n)).getOrElse(Set.empty)
        subscriptions((u,n)) = before + receiver
        val transformed = server.transformAnnotation(r.toInt, a) match {
          case Success(a) => a
          case Failure(e) =>
            log.error(e, "transformation of annotation failed")
            new Annotations()
        }
        receiver ! Annotated(info.id, u, transformed, n)
    }
    (subscriptions.keySet -- annotations.keySet).foreach {
      case (u,n) =>
        receiver ! AnnotationsOffered(info.id, u, n, descriptions.get((u,n)))
    }
  }

  def addSubscription(user: Long, name: String, peer: ActorRef) = {
    val before = subscriptions.get((user,name)).getOrElse(Set.empty)
    if (before.isEmpty) clients.find(_._2.id == user).foreach {
      case (r,i) => r ! AnnotationsRequested(info.id, name)
    }
    subscriptions((user,name)) = before + peer
    annotations.get((user,name)).foreach { case (rev,as) =>
      server.transformAnnotation(rev.toInt, as).foreach(peer ! Annotated(info.id,user,_,name))
    }
  }

  def removeSubscription(user: Long, name: String, peer: ActorRef) = {
    val before = subscriptions.get((user,name)).getOrElse(Set.empty)
    val after = before - peer
    if (before.nonEmpty && after.isEmpty) clients.find(_._2.id == user).foreach {
      case (r,i) => r ! AnnotationsDisregarded(info.id, name)
    }
    subscriptions((user,name)) = after
    peer ! AnnotationsClosed(info.id,user,name)
  }

  def receiveMessages: Receive = {
    case WithPath(Seq(),any) => receiveMessages(any)

    case ExplorePath =>
      context.parent.forward(BrowseFolder)

    case Messages.internal.OpenFile(user) =>
      log.info(s"opening for ${user.user}")
      if (!otActive) {
        try {
          initOt()
          clients += sender -> user
          context.watch(sender)
          sender ! Events.internal.OTState(this.info, server.text.mkString, server.revision)
          resendAnnotations(sender)
        }
        catch {
          case e: Throwable =>
            log.error(e, "init failed")
            sender ! FileInitFailed(this.info.id)
        }
      } else {
        clients += sender -> user
        context.watch(sender)
        sender ! Events.internal.OTState(this.info, server.text.mkString, server.revision)
        resendAnnotations(sender)
      }

    case Annotate(_,rev,as,name) if clients.isDefinedAt(sender) =>
      if (!otActive) initOt()
      val key = (clients(sender).id,name)
      if (!subscriptions.contains(key))
        subscriptions(key) = clients.keySet.toSet - sender
      if (!subscriptions(key).isEmpty) {
      server.transformAnnotation(rev.toInt, as) match { // TODO: Ugly: rev.toInt
        case Failure(e) =>
          // TODO
          log.warning("{}'s annotation could not be transformed", clients(sender).user)
        case Success(as) =>
          annotations.get((clients(sender).id,name)) match {
            case None =>
            case Some((oldRev,oldA)) =>
              server.transformAnnotation(oldRev.toInt, oldA).toOption match {
                case None      =>
                  log.warning("couldnt transform old annotations")
                  // TODO: Handle failure here
                case Some(old) =>
                  //val diff = AnnotationDiff.diff(old.annotations, a.annotations)
                  //log.info("diff for ({},{}): {}", clients(sender).id, name, diff)
                  //if (old.annotations != a.annotations)
                    //clients.keys.filter(_ != sender).foreach(_ ! AnnotationChanged(info.id,clients(sender).id,diff,name))
              }
          }

          clients.keys.filter(ref => ref != sender && subscriptions.get(key).exists(_.contains(ref))).foreach(_ ! Annotated(info.id,clients(sender).id,as,name))
          annotations(key) = (server.revision,as)
      }
      } else {
        annotations(key) = (rev,as)
      }

    case Edit(_,rev,ops) if clients.contains(sender) =>
      if (!otActive) initOt()
      server.applyOperation(ops,rev) match {
        case Failure(e) =>
          // TODO
          log.warning("edit couldnt be applied")
        case Success(o) =>
          DB.withSession { implicit session: Session => Revisions.create(info.id,server.revision,o) }
          clients.keys.filter(_ != sender).foreach(_ ! Edited(info.id, o))
          sender ! AcknowledgeEdit(info.id)
      }

    case SubscribeToAnnotations(_,user,name) if clients.contains(sender) =>
      addSubscription(user, name, sender)

    case UnsubscribeFromAnnotations(_,user,name) if clients.contains(sender) =>
      removeSubscription(user, name, sender)

    case OfferAnnotations(_,name,descr) if clients.contains(sender) =>
      val user = clients(sender).id
      subscriptions((user,name)) = Set.empty
      descr match {
        case None => descriptions.remove((user,name))
        case Some(d) => descriptions((user,name)) = d
      }
      clients.keys.filter(_ != sender).foreach(_ ! AnnotationsOffered(info.id,user,name,descr))

    case EOF =>
      subscriptions.filter(_._2.nonEmpty).keys.foreach {
        case (u,n) => removeSubscription(u, n, sender)
      }
      clients.remove(sender) match {
        case None =>
        case Some(c) =>
          annotations.filterKeys(_._1 == c.id).toList.foreach {
            case ((u,n),as) =>
              annotations.remove((u,n))
              subscriptions.remove((u,n)) match {
                case None =>
                case Some(subscribers) => subscribers.foreach(_ ! AnnotationsClosed(info.id,u,n))
              }
          }
      }

    case TouchFile =>
      //

    case Delete => // TODO !!
      info = info.copy(deleted = true)
      if (info.exists && !file.delete()) {
        DB.withSession { implicit session: Session => FileInfos.update(info) }
        file.deleteOnExit() // HACK: Schedule deletion instead
      } else {
        DB.withSession { implicit session: Session => FileInfos.delete(info) }
      }
      triggerFileEvent(FileDeleted(info))
      context.stop(self)

    case Terminated(ref) =>
      receive(EOF)

    case other => log.warning("unhandeled message: {}", other)
  }

  def receive = receiveMessages orElse receiveFileEvents

  override def preRestart(reason:Throwable, message:Option[Any]){
    log.error(reason, "Unhandled exception for message: {}", message)
  }

  override def preStart() {
    initFileEventSource()
    DB.withSession { implicit session: Session =>
      FileInfos.get(project, parent.path :+ name) match {
        case None => // The file did not previously exist
          info = FileInfos.create(FileInfo(
            project = project.id,
            path    = parent.path :+ name,
            mimeType = Try(mimeTypes.getString(name.split('.').last)).toOption,
            deleted = false,
            exists  = false,
            isDirectory = false,
            parent = Some(parent.id)
          ))
          log.info("file created: " + info)
          triggerFileEvent(FileCreated(info))
        case Some(info) =>
          if (info.deleted) { // The file was in a deleted state
            this.info = info.copy(deleted = false)
            FileInfos.update(this.info)
            log.info("file created: " + info)
            triggerFileEvent(FileCreated(this.info))
          } else {
            this.info = info
          }
      }
    }
  }
}
