package clide.client.util

import org.scalajs.dom._
import scala.scalajs.js
import clide.client.ui.html._

abstract class JsApp(rootId: String) extends DelayedInit {   
  val template: NodeFactory
      
  def delayedInit(body: => Unit) {
    def start() {      
      val rootNode = document.getElementById(rootId)
        if (rootNode == null) {
          console.error("root node is missing")
        } else {
          body
          template.create()(BodyNode)
        }
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
      window.document.onreadystatechange = readyEventHandler    
  }
}