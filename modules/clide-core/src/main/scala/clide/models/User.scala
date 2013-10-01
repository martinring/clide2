package clide.models

case class User(name: String, email: String) {
  override def equals(other: Any) = other match {
    case User(n,_) => name == n
    case _ => false
  }
}

trait Password { this: User =>
  val password: String
}

trait Projects { this: User =>
  val projects: Iterable[Project]
}

trait OtherProjects { this: User =>
  val otherProjects: Iterable[Project with AccessLevel]
}