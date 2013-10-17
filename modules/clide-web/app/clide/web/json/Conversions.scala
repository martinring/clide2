package clide.web.json

import play.api.libs.json._
import clide.models._
import clide.collaboration._
import clide.actors.Events._
import clide.actors.Messages.{CreateProject}

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
  
  implicit object AnnotationFormat extends Format[Annotation] {
    def reads(json: JsValue): JsResult[Annotation] = json match {
      case JsNumber(n) if n > 0      => JsSuccess(Plain(n.toInt))
      case obj: JsObject             => for {
        length <- (obj \ "l").validate[Int]
        content <- (obj \ "c").validate[Map[String,String]]
      } yield Annotate(length,content)
      case _ => JsError("cant parse action: expected number or object")
    }
    def writes(a: Annotation): JsValue = a match {
      case Plain(n) => JsNumber(n)
      case Annotate(n,c) => Json.obj("l" -> n, "c" -> c)      
    }
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
    case TimeOut => error("the request timed out")
    case Welcome => "welcome"
    case UnexpectedTermination => error("internal server error (unexpected termination)")
    case SignedUp(user) => "signedup" of user
    case LoggedIn(user,login) => "loggedin" of user
    case LoggedOut(user) => "loggedout"
    case FolderContent(folder,files) => Json.obj("t"->"folder","info"->folder,"files"->files)
    case CreatedProject(p) => "createdproject" of p
    case DeletedProject(p) => "deletedproject" of p.id
    case SessionInit(s,cs,conv) => Json.obj("t"->"welcome","info"->s,"others"->cs,"chat"->conv.map{case Talked(w,m,t) => Json.obj("s"->w,"m"->m,"t"->t)})
    case SessionChanged(s) => "session_changed" of s
    case SessionStopped(s) => "session_stopped" of s    
    case FileInitFailed(f) => "failed" of f
    case FileCreated(f) => "newfile" of f
    case FileDeleted(f) => "rmfile" of f
    case FileId(i) => "file" of i
    case FileSwitched(i) => "switch" of i
    case FileClosed(i) => "close" of i
    case FileOpened(i) => "opened" of i
    case Edited(file,o) => Json.obj("f"->file,"o"->o)
    case Annotated(file,user,a,name) => Json.obj("f"->file,"a"->a,"u"->user,"n"->name)
    case AcknowledgeEdit => JsString("ack_edit")
    case AcknowledgeAnnotation => JsString("ack_annotation")
    case NotAllowed => "e" of "internal error: forbidden action"
    case DoesntExist => "e" of "internal error: the referenced resource doesn't exist on the server"
    case Talked(w,m,t) => "talk" of Json.obj("s" -> w, "m" -> m,"t"->t)
    case _ => error("couldnt translate")
  }
}