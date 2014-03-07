package clide.client

import clide.reactive.ui._
import scala.scalajs.js.annotation.JSExport
import clide.reactive.Event
 
@JSExport  
object Example extends Html5App {
  val className = "test"
  val (counter,channel) = Event.broadcast[String]()
  @JSExport  
  def render = html"<div class='$className'>$counter</div>"
}