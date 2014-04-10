package clide.messages

object User {
  case object RequestProjectList
  case class ProjectList(names: List[String])
}