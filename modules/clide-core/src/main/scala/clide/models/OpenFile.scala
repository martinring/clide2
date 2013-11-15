package clide.models
  
case class OpenedFile(
    info: FileInfo, 
    state: String, 
    revision: Long) {
  override def equals(other: Any) = other match {
    case OpenedFile(file,_,_) => file == info
    case _ => false
  }
}

