package clide.models

case class SessionInfo(
    id: Long,
    user: String,
    color: String,
    project: Long,
    activeFile: Option[Long],    
    active: Boolean) {
  override def equals(other: Any) = other match {
    case SessionInfo(id,_,_,_,_,_) => id == this.id
    case _ => false
  }
}