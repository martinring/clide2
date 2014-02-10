package clide.client.util

import scala.scalajs.js
import clide.client.ui.html._
import org.scalajs.dom.document

abstract class JsApp(rootId: String) extends DelayedInit {   
  val template: NodeFactory
      
  def delayedInit(body: => Unit) {
    def start() {            
      body
      val node = Node(rootId)
      node.clear()
      template.create()(node)        
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