package clide.client

import clide.reactive.ui._
import clide.reactive.ui.html.HTML5
import scala.scalajs.js.annotation.JSExport
import clide.reactive.Event
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.language.reflectiveCalls
import scala.language.existentials
import org.scalajs.dom

@JSExport
object App { 
  dom.document.body.innerHTML = ""
 
  implicit val body = InsertionContext.append(dom.document.body)
  implicit val executionContext = scalajs.concurrent.JSExecutionContext.queue

  val test = 
    <xml a="4">
      <a>
      </a>
      <b>
      </b>
    </xml>
}