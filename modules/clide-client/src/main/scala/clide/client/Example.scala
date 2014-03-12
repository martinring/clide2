package clide.client

import clide.reactive.ui._
import scala.scalajs.js.annotation.JSExport
import clide.reactive.Event
import scala.concurrent.duration._
import scala.language.postfixOps
import clide.reactive.ui.events.DOMEvent
import org.scalajs.dom
import clide.reactive.ui.HTMLMacro._

@JSExport  
object Example {
  implicit val ec = scalajs.concurrent.JSExecutionContext.runNow
  implicit val scheduler = clide.reactive.ui.UiScheduler

  dom.document.body.innerHTML = ""
  
  val x = "itWorks"
    
  def parameterized(time: Long) = html"<span>Hallo $time</span>" 
    
  val view = html"""
    <div id='$x'>
      <input model:username='value' event:usernameChange='input' type='text' placeholder='username'></input><br/>
      <input model:password='value' type='password' placeholder='password'></input>
    </div>
    <div>Hier: ${Event.interval(2 seconds).map(parameterized)}</div>
  """.render(InsertionContext.append(dom.document.body))
   
  import view._

  username_=("test")
  password_=("something else")
  usernameChange.sample(username).foreach(password_=)
  
  @JSExport
  def destroy() = view.destroy()
} 