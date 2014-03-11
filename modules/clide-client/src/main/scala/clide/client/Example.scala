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
  val x = 4

  @JSExport
  def fragment = html"<div>it $x works $x good</div><div>Hallo?</div>"
} 