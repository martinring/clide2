package clide.client.ui

import scala.language.implicitConversions
import clide.client.util.Cancellable
import clide.client.rx.Observable

package object html {
  trait Control
  trait Span extends Control
  trait Input extends Control
  trait CheckBox extends Input
  trait TextBox extends Input
  trait Select extends Input
  trait LinkLike extends Control
  trait Button extends LinkLike
  trait Link extends LinkLike
  trait List extends Control
  trait ListItem extends Control
  trait Form extends Control
  trait Label extends Span
  
  val id        = Attribute[String,Control]("id")
  val name      = Attribute[String,Control]("name")
  val className = Attribute[String,Control]("className")
  val title     = Attribute[String,Control]("title")
  val click     = Event.named[Unit,Control]("click")
  val hidden    = Attribute.flag[Control]("hidden")
  
  def showWhen(obs: Observable[Boolean]) = BoundAttribute[Control] { t =>
    val initial = t.style.getPropertyValue("display")
    obs.observe(show => if (show) t.style.setProperty("display", initial) else t.style.setProperty("display", "none"))
  }

  object Div extends Tag[Control]("div")
  object Form extends Tag[Control]("form")
  
  object Span extends Tag[Span]("span")  
  val text = Attribute[String,Span]("textContent")
  
  object Small extends Tag[Span]("small")  
  
  object Label extends Tag[Label]("label")
  val labelFor = Attribute[String,Label]("for")
  
  object Paragraph extends Tag[Span]("p")
  case class Heading(level: Int) extends Tag[Span]("h" + level)
  
  object Button extends Tag[Button]("button")
  val disabled = Attribute.flag[LinkLike]("disabled")
  val buttonType = Attribute[String,Button]("type")
  
  implicit def actionLink(action: Action) = BoundAttribute[LinkLike] { t =>
    val a = (click triggers action).attach(t)
    val b = (disabled <-- action.executable.map(!_).startWith(true)).attach(t)
    Cancellable { a.cancel(); b.cancel() }
  }
  
  object Link extends Tag[Link]("a")
  val href = Attribute[String,Link]("href")  
  val noref = href := "#"
    
  object TextBox extends Tag[TextBox]("input")
  object PasswordBox extends Tag[TextBox]("input", inputType := "password")
  val placeholder = Attribute[String,TextBox]("placeholder")
  val inputType = Attribute[String,Input]("type")
  val value = Attribute[String,TextBox]("value")
  val input = Event.named[Unit,TextBox]("input")
  
  object CheckBox extends Tag[CheckBox]("input", inputType := "checkbox")
  val checked = Attribute.bool[CheckBox]("checked")
  
  object Select extends Tag[Select]("select")
  val select = Event.named[Unit,Select]("select")
  
  object UnorderedList extends Tag[List]("ul")
  object OrderedList extends Tag[List]("ol")  
    
  object ListItem extends Tag[ListItem]("li")
  
  object PreFormated extends Tag[Span]("pre") 
}