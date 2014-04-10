package clide.client

import scala.concurrent.duration._
import scala.collection.mutable.ArrayBuffer
import clide.xml._
import clide.reactive._
import clide.reactive.ui._
import scalajs.js.annotation.JSExport
import org.scalajs.dom
  
@JSExport
object App extends clide.reactive.ui.App with History { 
  dom.document.body.innerHTML = ""     
  
  val BackstagePath = "/([A-Za-z0-9 ]+)/backstage".r
    
  def titles = history.items.map {
    case "/login" => "Log In"
    case "/signup" => "Sign Up"
    case BackstagePath(user) => user + "'s Backstage"
  }
    case x if x.startsWith("/login") => title = "Login"
    case _ => title = "Somewhere else"
  }
    
  def basics = {   
    val name = Var("World")
    XML.include(HTML5,"basics.html") 
  } 
    
  def todos = {
    class Todo(val text: String, val done: Boolean)
    lazy val todos = ObservableBuffer(
      new Todo("learn scala.js", true), 
      new Todo("build a scala.js app", false))
    def remaining = todos.changes.sample(todos.count(!_.done).toString)
    def total = todos.watch.length.map(_.toString)
    def archive() = todos.replaceAll(todos.filter(!_.done))
    def setDone(todo: Todo)(value: Boolean) =
      todos(todos.indexOf(todo)) = new Todo(todo.text, value)
    def addTodo(text: String) = todos += new Todo(text,false)
    XML.include(HTML5,"todo.html")
  }
  
  dom.document.body.appendChild(basics)
  dom.document.body.appendChild(todos)
}