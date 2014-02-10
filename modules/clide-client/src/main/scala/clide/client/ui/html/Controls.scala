package clide.client.ui.html

trait Control
trait Span extends Control
trait TextBox extends Control
trait Button extends Control

object Control {
  val id        = Attribute[String,Control]("id")
  val className = Attribute[String,Control]("className")
  val title     = Attribute[String,Control]("title")  
}

object Div extends Tag[Control]("div")

object Span extends Tag[Span]("span") {  
  val text = Attribute[String,Span]("textContent")
}

object P extends Tag[Span]("p")
object H1 extends Tag[Span]("h1")
object H2 extends Tag[Span]("h2")
object H3 extends Tag[Span]("h3")
object H4 extends Tag[Span]("h4")
object Button extends Tag[Button]("button") {
  val onClick = Event[Unit,Button]("click")
}
object TextBox extends Tag[TextBox]("input") {
  val value = Attribute[String,TextBox]("value")
  val onInput = Event[Unit,TextBox]("input")
}