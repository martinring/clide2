package clide.messages.users

import clide.messages.projects.ProjectInfo

object User {
  case object RequestProjectList
  case class ProjectList(items: List[ProjectInfo])
}