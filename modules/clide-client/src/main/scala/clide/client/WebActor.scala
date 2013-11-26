package clide.client

import org.scalajs.dom._

abstract class WebActor(url: String) {
  private val socket = new WebSocket(url)  
  type Receive = PartialFunction[Any,Unit]
  def receive: Receive  
  object Terminated
  socket.onmessage = { e =>
    
  }
  socket.onclose = { e =>
    
  }
  
}