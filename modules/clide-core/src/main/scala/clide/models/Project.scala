package clide.models

case class Project(owner: String, name:  String, description: Option[String], id: Option[Long]) {
  override def equals(other: Any) = other match {
    case Project(_,_,_,id@Some(_)) => id == this.id
    case _ => false
  }
}

trait Collaborators { this: Project =>
  val collaborators: Iterable[User with AccessLevel]
}

trait AccessLevel {
  val accessLevel: AccessLevel.Value
}

object AccessLevel extends Enumeration {
  val None, Read, Write, Admin = Value
}