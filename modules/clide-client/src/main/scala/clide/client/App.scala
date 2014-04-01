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
     
  { 
    dom.document.body.innerHTML = ""
      
	  val subject = "dlroW" 
	  val counter = Event.interval(1 second)
	  val items = ObservableBuffer("Hallo","Test")

	  dom.document.body.appendChild(XML.include(HTML5,"backstage.html"))
  }
  
  {
    dom.document.body.appendChild(XML.include(HTML5,"basics.html"))
  }
}