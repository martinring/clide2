package clide.client.ui

import scala.language.implicitConversions
import clide.client.util.Cancellable

package object html {
  trait Control
  trait Span extends Control
  trait TextBox extends Control
  trait Select extends Control
  trait LinkLike extends Control
  trait Button extends LinkLike
  trait Link extends LinkLike
  
  val id        = Attribute[String,Control]("id")
  val className = Attribute[String,Control]("className")
  val title     = Attribute[String,Control]("title")
  val click   = Event.named[Unit,Control]("click")

  object Div extends Tag[Control]("div")
  
  object Span extends Tag[Span]("span")  
  val text = Attribute[String,Span]("textContent")  
  
  object P extends Tag[Span]("p")
  object H1 extends Tag[Span]("h1")
  object H2 extends Tag[Span]("h2")
  object H3 extends Tag[Span]("h3")
  object H4 extends Tag[Span]("h4")
  object Button extends Tag[Button]("button")
  val disabled = Attribute.flag[LinkLike]("disabled")
  
  implicit def actionLink(action: Action) = BoundAttribute[LinkLike] { t =>
    val a = (click triggers action).attach(t)
    val b = (disabled <-- action.executable.map(!_).startWith(true)).attach(t)
    Cancellable { a.cancel(); b.cancel() }
  }
  
  object Link extends Tag[Link]("a")
  val href = Attribute[String,Link]("href")  
  val noref = href := "#"
    
  object TextBox extends Tag[TextBox]("input")
  val value = Attribute[String,TextBox]("value")
  val input = Event.named[Unit,TextBox]("input")
  
  object Select extends Tag[Select]("select")
  val select = Event.named[Unit,Select]("select")
}