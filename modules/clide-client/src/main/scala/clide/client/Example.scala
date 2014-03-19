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
  
  @view class ProjectView(project: Project) {
    html"""
      <div>
        <span>${project.name}</span>
      </div>
    """
  }
  
  @view class PersonView(name: String, age: Int) {    
    html"""
      <div class='test'>
        <span text='@name'>$name (${age.toString})</span>
        <input type='text' placeholder='test' ng:bind="${passwordBox.textChange}"></input>
        <input type='password' scala:name='passwordBox'></input>
        Hallo, dein passwort ist: ${passwordBox.textChange.map(pwd => new ProjectView(Project(pwd)))}
      </div>
    """

    def password = passwordBox.value
  }
  
  case class Project(name: String) 
  
  val a = new PersonView("Martin",27)  
}