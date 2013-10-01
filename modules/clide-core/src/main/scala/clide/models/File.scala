package clide.models

sealed trait Path

sealed trait FolderPath extends Path {
  def / (folder: String): FolderPath  = Subfolder(this, folder)
  def /> (file: String): FilePath = FilePath(this, file)
}

case object ProjectRoot extends FolderPath {
  override def toString = "/"
}

case class Subfolder(parent: FolderPath, name: String) extends FolderPath {
  override def toString = s"${parent.toString}/$name"
}

case class FilePath(parent: FolderPath, name: String) extends Path {
  override def toString = s"${parent.toString}/$name"
}

object Test {
  ProjectRoot / "app" / "files" /> "test.thy"
}