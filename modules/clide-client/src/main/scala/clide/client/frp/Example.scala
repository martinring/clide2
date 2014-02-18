package clide.client.frp

import org.scalajs.dom._

object Example {
  var mouseDown = false
  var mouseDownRead = false
  addEventListener("mousedown", (e: org.scalajs.dom.Event) => {
    mouseDown = true
  })
  addEventListener("mouseup", (e: org.scalajs.dom.Event) => {
    mouseDown = false
  })
  
  val b: Behavior[String] = Event.step("Hallo", Event.mouseClicks ->> "Blub")
  
  setInterval(() => {
    
  }, 30)
}