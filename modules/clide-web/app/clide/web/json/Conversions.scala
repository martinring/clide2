 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 **                                                                           **
 **  This file is part of Clide.                                              **
 **                                                                           **
 **  Clide is free software: you can redistribute it and/or modify            **
 **  it under the terms of the GNU General Public License as published by     **
 **  the Free Software Foundation, either version 3 of the License, or        **
 **  (at your option) any later version.                                      **
 **                                                                           **
 **  Clide is distributed in the hope that it will be useful,                 **
 **  but WITHOUT ANY WARRANTY; without even the implied warranty of           **
 **  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
 **  GNU General Public License for more details.                             **
 **                                                                           **
 **  You should have received a copy of the GNU General Public License        **
 **  along with Clide.  If not, see <http://www.gnu.org/licenses/>.           **
 \*                                                                           */

package clide.web.json

import play.api.libs.json._
import clide.models._
import clide.collaboration._
import clide.actors.Events._
import clide.actors.Messages.{CreateProject}
import clide.collaboration.AnnotationDiff._
import play.api.data.validation.ValidationError
import scala.language.implicitConversions
import scala.language.reflectiveCalls

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

  def packAnnotations(as: Set[(AnnotationType.Value,String)]): Map[String,Seq[String]] = {
    val packed = for {
      key <- as.map(_._1)
    } yield key -> as.filter(_._1 == key).map(_._2)

    packed.toMap.map {
      case (k,v) => k.toString -> v.toSeq
    }
  }

  def unpackAnnotations(as: Map[String,Seq[String]]): Set[(AnnotationType.Value,String)] = {
    val unpacked = as.toSeq.flatMap {
      case (k,v) =>
        val a = AnnotationType.withName(k)
        v.map { v =>
          a -> v
        }
    }
    unpacked.toSet
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

  implicit object AnnotationDiffItemWrites extends Writes[AnnotationDiffItem] {
    def writes(a: AnnotationDiffItem): JsValue = a match {
      case Leave(n) => JsNumber(n)
      case Replace(n,c) => Json.obj("l"->n,"c"->c)
    }
  }

  implicit object AnnotationDiffWrites extends Writes[AnnotationDiff] {
    def writes(a: AnnotationDiff): JsValue =
      Json.toJson(a.items)
  }

  implicit object AnnotationsFormat extends Format[Annotations] {
    def reads(json: JsValue) =
      Json.fromJson[List[Annotation]](json).map(Annotations.apply)
    def writes(value: Annotations) =
      Json.toJson(value.annotations)
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
    case TimeOut                => error("the request timed out")
    case Welcome                => "welcome"
    case UnexpectedTermination  => error("internal server error (unexpected termination)")
    case SignedUp(user)         => "signedup" of user
    case LoggedIn(user,login)   => "loggedin" of user
    case LoggedOut(user)        => "loggedout"
    case FolderContent(folder,files) => Json.obj("t"->"folder","info"->folder,"files"->files)
    case CreatedProject(p)      => "createdproject" of p
    case DeletedProject(p)      => "deletedproject" of p.id
    case SessionInit(s,cs,conv) => Json.obj("t"->"welcome","info"->s,"others"->cs,"chat"->conv.map{case Talked(w,m,t,tp) => Json.obj("s"->w,"m"->m,"t"->t,"tp"->tp)})
    case SessionChanged(s) => "session_changed" of s
    case SessionStopped(s) => "session_stopped" of s
    case FileInitFailed(f) => "failed" of f
    case FileCreated(f)    => "newfile" of f
    case FileDeleted(f)    => "rmfile" of f
    case FileId(i)         => "file" of i
    case FileSwitched(i)   => "switch" of i
    case FileClosed(i)     => "close" of i
    case FileOpened(i)     => "opened" of i
    case Edited(file,o)    => Json.obj("f"->file,"o"->o)
    case Annotated(file,user,a,name)         => Json.obj("f"->file,"a"->a,"u"->user,"n"->name)
    // TODO: case AnnotationChanged(file,user,a,name) => Json.obj("f"->file,"ac"->a,"u"->user,"n"->name)
    case AcknowledgeEdit(f) => JsNumber(f)
    case NotAllowed    => "e" of "internal error: forbidden action"
    case DoesntExist   => "e" of "internal error: the referenced resource doesn't exist on the server"
    case Talked(w,m,t,tp) => "talk" of Json.obj("s" -> w, "m" -> m,"t"->t,"tp"->tp)
    case UserProjectInfos(own, other)                  => "projects" of Json.obj("own"->own, "other"->other)
    case ChangedProjectUserLevel(project, user, level) => "access" of Json.obj("p"->project,"u"->user,"l"->level.id)
    case _ => error("couldnt translate")
  }
}
