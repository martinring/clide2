package clide.client

import clide.reactive.ui.html.HTML5
import scala.scalajs.js.annotation.JSExport
import clide.reactive.Event
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.language.reflectiveCalls
import scala.language.existentials
import org.scalajs.dom
import clide.xml._
import clide.reactive.ui.InsertionContext
import scala.collection.mutable.ArrayBuffer
import clide.reactive.ObservableBuffer

@JSExport  
object App {    
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.queue
  implicit val scheduler = clide.reactive.ui.UiScheduler
  
  dom.document.body.innerHTML = ""
     
  def basics =
    XML.include(HTML5,"basics.html")  
    
  def todos = {
    case class Todo(text: String, done: Boolean)
    val todos = ObservableBuffer(Todo("learn angular", true),
                                 Todo("build an angular app", false))
    def remaining = todos.count(!_.done)
    def archive() = todos.foreach(todo => if (todo.done) todos -= todo)
    def update(todo: Todo, donen: Boolean) = {
      println("Hallo")
      todos(todos.indexOf(todo)) = todo.copy(done = donen)
    }
    def addTodo(text: String) = todos += Todo(text,false)
    XML.include(HTML5,"todo.html") 
  }
  
  dom.document.body.appendChild(basics)  
  dom.document.body.appendChild(todos)
}