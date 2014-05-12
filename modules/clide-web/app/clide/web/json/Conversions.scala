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

package clide.web.json

import play.api.libs.json._
import clide.models._
import clide.collaboration._
import clide.actors.Events._
import clide.actors.Messages.{CreateProject}
import play.api.data.validation.ValidationError
import scala.language.implicitConversions
import scala.language.reflectiveCalls
import clide.actors.Messages.{WorkingOnFile,DoneWithFile,FailureInFile,LookingAtFile,StoppedLookingAtFile}
import clide.actors.Messages.Talk

object Conversions {
  implicit object FileInfoWrites extends Writes[FileInfo] {
    def writes(f: FileInfo) = Json.obj(
        "id" -> f.id,
        "name" -> f.path.lastOption,
        "project" -> f.project,
        "path" -> f.path,
        "mimeType" -> f.mimeType,
        "deleted" -> f.deleted,
        "exists" -> f.exists,
        "isDirectory" -> f.isDirectory,
        "parent" -> f.parent)
  }

  implicit val OpenedFileWrites = Json.writes[OpenedFile]

  implicit val ProjectInfoWrites = Json.writes[ProjectInfo]

  implicit val SessionInfoWrites = Json.writes[SessionInfo]

  implicit object UserInfoWritesWrites extends Writes[UserInfo] {
    def writes(u: UserInfo) = Json.obj(
        "name"  -> u.name,
        "email" -> u.email)
  }

  def packAnnotations(as: List[(AnnotationType.Value,String)]): Map[String,Seq[String]] = {
    val packed = for {
      key <- as.map(_._1)
    } yield key -> as.filter(_._1 == key).map(_._2)

    packed.toMap.map {
      case (k,v) => k.toString -> v.toSeq
    }
  }

  def unpackAnnotations(as: Map[String,Seq[String]]): List[(AnnotationType.Value,String)] = {
    val unpacked = as.toSeq.flatMap {
      case (k,v) =>
        val a = AnnotationType.withName(k)
        v.map { v =>
          a -> v
        }
    }
    unpacked.toList
  }

  implicit object AnnotationFormat extends Format[Annotation] {
    def reads(json: JsValue): JsResult[Annotation] = json match {
      case JsNumber(n) if n > 0      => JsSuccess(Plain(n.toInt))
      case obj: JsObject             => for {
        length  <- (obj \ "l").validate[Int]
        content <- (obj \ "c").validate[Map[String,List[String]]]
      } yield Annotate(length,unpackAnnotations(content))
      case _ => JsError("cant parse action: expected number or object")
    }
    def writes(a: Annotation): JsValue = a match {
      case Plain(n) => JsNumber(n)
      case Annotate(n,c) => Json.obj("l" -> n, "c" -> packAnnotations(c))
    }
  }

  implicit object AnnotationsFormat extends Format[Annotations] {
    def reads(json: JsValue) =
      Json.fromJson[List[Annotation]](json).map(Annotations(_))
    def writes(value: Annotations) =
      Json.obj("as" -> value.annotations, "rs" -> value.responses.map(r => Json.obj("r" -> r._1, "a" -> r._2)))
  }

  implicit object ActionFormat extends Format[Action] {
    def reads(json: JsValue): JsResult[Action] = json match {
      case JsNumber(n) if n > 0      => JsSuccess(Retain(n.toInt))
      case JsNumber(n) if n < 0      => JsSuccess(Delete(-n.toInt))
      case JsString(s) if s.nonEmpty => JsSuccess(Insert(s))

      case _                         => JsError("cant parse action: expected number, string or object")
    }
    def writes(action: Action): JsValue = action match {
      case Retain(n) => JsNumber(n)
      case Delete(n) => JsNumber(-n)
      case Insert(s) => JsString(s)
    }
  }

  implicit object OperationFormat extends Format[Operation] {
    def reads(json: JsValue) =
      Json.fromJson[List[Action]](json).map(Operation.apply)
    def writes(value: Operation) =
      Json.toJson(value.actions)
  }

  implicit val CreateProjectReads = Json.reads[CreateProject]

  private def error(error: String) = Json.obj("t"->"e","c"->error)

  private implicit def jsontype(name: String) = new {
    def of[T](content: T)(implicit writes: Writes[T]) = Json.obj("t"->name,"c"->content)
  }

  private implicit def plain(name: String) = Json.obj("t"->name)
  
  def serializeEvent(event: Event): JsValue = event match {
    case BroadcastEvent(who,when,Talk(w,m,tp))            => "talk" of Json.obj("s" -> who, "t" -> when, "m" -> m, "tp" -> tp)
    case BroadcastEvent(who,when,WorkingOnFile(f))        => "process" of Json.obj("f"->f,"u"->who,"t"->"w")
    case BroadcastEvent(who,when,DoneWithFile(f))         => "process" of Json.obj("f"->f,"u"->who,"t"->"d")
    case BroadcastEvent(who,when,FailureInFile(f,msg))    => "process" of Json.obj("f"->f,"u"->who,"t"->"f","m"->msg)
    case BroadcastEvent(who,when,LookingAtFile(f))        => "process" of Json.obj("f"->f,"u"->who,"t"->"l")
    case BroadcastEvent(who,when,StoppedLookingAtFile(f)) => "process" of Json.obj("f"->f,"u"->who,"t"->"i")
    case TimeOut                => error("the request timed out")
    case Welcome                => "welcome"
    case UnexpectedTermination  => error("internal server error (unexpected termination)")
    case SignedUp(user)         => "signedup" of user
    case LoggedIn(user,login)   => "loggedin" of user
    case LoggedOut(user)        => "loggedout"
    case FolderContent(folder,files) => Json.obj("t"->"folder","info"->folder,"files"->files)
    case CreatedProject(p)      => "createdproject" of p
    case DeletedProject(p)      => "deletedproject" of p.id
    case SessionInit(s,cs,conv) => Json.obj("t"->"welcome","info"->s,"others"->cs,"events"->conv.map(serializeEvent))
    case SessionChanged(s) => "session_changed" of s
    case SessionStopped(s) => "session_stopped" of s
    case FileInitFailed(f) => "failed" of f
    case FileCreated(f)    => "newfile" of f
    case FileDeleted(f)    => "rmfile" of f
    case FileId(i)         => "file" of i    
    case FileClosed(i)     => "close" of i
    case FileOpened(i)     => "opened" of i
    case Edited(file,o)    => Json.obj("f"->file,"o"->o)
    case Kicked            => "kicked"
    case AnnotationsOffered(file,user,name,descr) => Json.obj("t"->"ao","f"->file,"u"->user,"n"->name,"d"->descr)
    case Annotated(file,user,a,name)         => Json.obj("f"->file,"a"->a,"u"->user,"n"->name)
    case AnnotationsClosed(file,user,name)   => Json.obj("t"->"ac","f"->file,"u"->user,"n"->name)
    // TODO: case AnnotationChanged(file,user,a,name) => Json.obj("f"->file,"ac"->a,"u"->user,"n"->name)
    case AcknowledgeEdit(f) => JsNumber(f)
    case NotAllowed    => "e" of "internal error: forbidden action"
    case DoesntExist   => "e" of "internal error: the referenced resource doesn't exist on the server"
    case UserProjectInfos(own, other)                  => "projects" of Json.obj("own"->own, "other"->other)
    case ChangedProjectUserLevel(project, user, level) => "access" of Json.obj("p"->project,"u"->user,"l"->level.id)
    case e => "lit" of e.toString
  }
}
