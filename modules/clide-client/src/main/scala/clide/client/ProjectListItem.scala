package clide.client

import clide.client.ui._

case class Project(owner: String, name: String)

class ProjectListItem(val data: Project) extends DataTemplate[Project] {
  val template = Div(className := "item")(
      Span(className := "owner")("data.owner"), "/", 
      Span(className := "name")("data.name"))
}