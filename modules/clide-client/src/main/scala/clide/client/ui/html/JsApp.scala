package clide.client.ui.html

import scala.scalajs.js
import clide.client.ui.html._
import scala.scalajs.js.Any.fromFunction1
import org.scalajs.dom.document
import org.scalajs.dom.HTMLElement

abstract class JsApp extends DelayedInit {   
  val template: NodeFactory   
  
  def delayedInit(body: => Unit) {
    def start() {            
      body      
      Body.clear()      
      template.create()(Body)
    }
    
    val readyEventHandler: js.Function1[org.scalajs.dom.Event,Unit] = (e: org.scalajs.dom.Event) => {
      if (document.readyState == "interactive".asInstanceOf[js.String] ||
          document.readyState == "complete".asInstanceOf[js.String]) {
        document.onreadystatechange = null        
        start()
      }
    }    
    
    if (document.readyState == "interactive".asInstanceOf[js.String] 
     || document.readyState == "complete".asInstanceOf[js.String])
      start()
    else
      document.onreadystatechange = readyEventHandler    
  }
}