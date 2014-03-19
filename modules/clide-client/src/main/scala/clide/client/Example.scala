package clide.client

import clide.reactive.ui._
import scala.scalajs.js.annotation.JSExport
import clide.reactive.Event
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.language.reflectiveCalls
import scala.language.existentials
import org.scalajs.dom

@JSExport
object Example {
  dom.document.body.innerHTML = ""

  implicit val insertionContext = InsertionContext.append(dom.document.body)
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.queue

  object ng {
    def hallo(elem: dom.HTMLElement, value: String) =
      elem.textContent = elem.textContent + value

    def bind(elem: dom.HTMLInputElement, value: Event[String]) =
      value.foreach(elem.value = _)
  }
  
  @view class PersonView(name: String, age: Int) {
    def credentials = (username.value, password.value)
    val hallo = () => password.value
    
    html"""
      <div class='test'>
        <span>$name ($age)</span>
        <input type='text' placeholder='test' ng:bind="${password.textChange}" scala:name='username'></input>
        <input type='password' scala:name='password'></input>
      </div>
    """
  }
  
  val a = new PersonView("Martin",27)
}