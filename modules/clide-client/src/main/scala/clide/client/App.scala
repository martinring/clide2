package clide.client

import scala.concurrent.duration._
import scala.collection.mutable.ArrayBuffer
import clide.xml._
import clide.reactive._
import clide.reactive.ui._
import scalajs.js.annotation.JSExport
import org.scalajs.dom

@JSExport
object App extends UiApp {
  dom.document.body.innerHTML = ""
     
  def basics =
    XML.include(HTML5,"basics.html")  
    
  def todos = {
    lazy val todos = ObservableBuffer(Todo("learn scala.js", true),
                                     Todo("build a scala.js app", false))

    case class Todo(val text: String, done: Boolean)
    
    // allow todos to be mutated
    implicit class MutableTodo(todo: Todo) {
      def done_=(value: Boolean) = 
        todos.update(todos.indexOf(todo), todo.copy(done = value))
    }
     
    def remaining = todos.count(!_.done)
    
    def archive() = todos.replaceAll(todos.filter(!_.done))
    
    def addTodo(text: String) = todos += new Todo(text,false)
    
    XML.include(HTML5,"todo.html") 
  }
  
  dom.document.body.appendChild(basics)  
  dom.document.body.appendChild(todos)
}