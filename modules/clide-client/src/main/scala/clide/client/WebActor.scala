package clide.client

import clide.client.libs._

abstract class WebActor(url: String) {
  private val socket = new WebSocket(url)
  type Receive = PartialFunction[Any,Unit]
  
  def receive: Receive
  
  object Terminated
  
  socket.onmessage = { e: MessageEvent =>
    val msg = angular.fromJson(e.data.asInstanceOf[String])
  }
  
  socket.onclose = { e: CloseEvent =>
    
  }
  
  socket.onopen = { e: Event =>
    
  }
  
  socket.onerror = { e: ErrorEvent =>
    
  }
}