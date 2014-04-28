package clide.core.users

import clide.core.projects.ProjectInfo

object User {
  case object RequestProjectList
  case class ProjectList(items: List[ProjectInfo])
}