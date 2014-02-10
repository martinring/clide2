package clide.client.ui.html

trait Control
trait TextBox extends Control
trait Button extends Control

object Control {
  val id        = Attribute[String,Control]("id")
  val className = Attribute[String,Control]("className")
  val title     = Attribute[String,Control]("title")
}

object Div extends Tag[Control]("div")
object Span extends Tag[Control]("span")
object Button extends Tag[Button]("button")
object TextBox extends Tag[TextBox]("input") {
  val value = Attribute[String,TextBox]("value")
  val onInput = Event[Unit,TextBox]("input")
}