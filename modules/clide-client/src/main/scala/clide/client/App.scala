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

@JSExport
object App {
  dom.document.body.innerHTML = ""

  def view = XML.include(HTML5,"backstage.html") {
    def user = "Martin"
  }

  dom.document.body.appendChild(view)
}