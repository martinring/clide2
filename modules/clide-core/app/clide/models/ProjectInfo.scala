package clide.models

case class ProjectInfo(
    id: Long,
    name: String,
    owner: String,
    description: Option[String] = None) {
  lazy val root = f"files/$owner/$name" // TODO: This should be configured in the future  
}