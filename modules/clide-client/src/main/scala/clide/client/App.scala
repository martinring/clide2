package clide.client

import scala.concurrent.duration._
import scala.collection.mutable.ArrayBuffer
import clide.xml._
import clide.reactive._
import clide.reactive.ui._
import scalajs.js.annotation.JSExport
import org.scalajs.dom
import clide.reactive.ui.JSApp
  
// Experimental Stuff
@JSExport
object App extends JSApp with History {
  /*
  dom.document.body.innerHTML = ""
  
  val BackstagePath = "/([A-Za-z0-9 ]+)/backstage".r
    
  def titles = history.items.map {
    case "/login" => "Log In"
    case "/signup" => "Sign Up"
    case BackstagePath(user) => user + "'s Backstage"
    case x if x.startsWith("/login") => title = "Login"
    case _ => title = "Somewhere else"
  }  

  def basics(intialName: String) = {    
    val name = Var(intialName)
    XML.include(HTML5,"basics.html") 
  }
    
  def todos = {
    case class Todo(text: String, done: Boolean)
    
    lazy val todos = ObservableBuffer(
      Todo("learn scala.js", true), 
      Todo("build a scala.js app", false))
      
    def remaining = todos.watch.count(!_.done)
    def total     = todos.watch.length.toStrings
    
    def archive() = todos.clear(_.done)
    
    def setDone(todo: Todo)(value: Boolean) =
      todos(todos.indexOf(todo)) = Todo(todo.text, value)
      
    def addTodo(text: String) = todos += Todo(text,false)
    
    XML.include(HTML5,"todo.html")
  }
  
  dom.document.body.appendChild(todos)
  dom.document.body.appendChild(basics("World"))
  
  */
}