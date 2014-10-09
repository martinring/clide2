package clide.reactive.ui

import scalajs.js
import org.scalajs.dom
import clide.reactive.Event

trait History extends DelayedInit { self: JSApp =>
  object history {
    private [History] val (event,channel) = Event.broadcast[String]()
    channel.push(dom.location.pathname)
    val items = event
  }
  
  abstract override def delayedInit(body: => Unit) {   
    super.delayedInit {
      dom.addEventListener("click", (e: dom.Event) => {
        println("something clicked")
		    val event = e.asInstanceOf[dom.MouseEvent]
		    event.target match {
          // a.origin is not available in some modern browsers yet so we user protocol + host
		      case html.Anchor(a) if a.protocol + a.host == dom.location.protocol + dom.location.host =>
		        event.preventDefault()
		        dom.history.pushState(null, a.title, a.pathname)
		        history.channel.push(a.pathname)
		        println("link clicked: " + a.href)
		      case _ => // do nothing
		    }
		  })
		  dom.addEventListener("popstate", (e: dom.Event) => {
		    val event = e.asInstanceOf[dom.PopStateEvent]
		    event.preventDefault()
		    history.channel.push(dom.location.pathname)
		  })
		  body
    }
  }  
}