package clide.messages.projects

import scala.concurrent.Future
import clide.messages.Ref

object Files {
  case class File(
    id: Int,
    name: String,
    natures: Set[String],
    folder: Option[Ref[Folder,Int]])
    
  case class Folder(
    id: Int,
    name: String,
    folders: Set[Ref[Folder,Int]],
    files: Set[Ref[File,Int]])
}