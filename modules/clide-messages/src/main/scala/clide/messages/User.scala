package clide.messages

object User {
  case object GetProjectInfos
  
  case class ProjectInfos(names: List[String])
}