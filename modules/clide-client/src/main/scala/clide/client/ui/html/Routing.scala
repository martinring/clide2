package clide.client.ui.html

import org.scalajs.dom._
import clide.client.rx._
import scala.scalajs.js

trait Routing extends JsApp {
  override def delayedInit(body: => Unit): Unit = super.delayedInit{
    body
    Location.init()
  }
  
  object Location {
    def back() = window.history.back()
    def forward() = window.history.forward()
    def path: Observable[String] = loc.startWith(window.location.pathname.asInstanceOf[String]).varying
    def path_=(path: String) = {
      loc.onNext(path)
      window.history.pushState(null, path, path)
    } 
    
    private val loc = Subject[String](window.location.pathname)
    private[Routing] def init() {
      window.addEventListener("popstate", (e: org.scalajs.dom.Event) => {
        loc.onNext(window.location.pathname)
      })
      document.body.addEventListener("click", (e: org.scalajs.dom.Event) => {
        val me = e.asInstanceOf[MouseEvent]
        if (!me.ctrlKey 
         && !me.metaKey 
         && me.button != 2.asInstanceOf[js.Number] 
         && me.srcElement.nodeName.toLowerCase() == "a".asInstanceOf[js.String]) {
          val href = me.srcElement.getAttribute("href")
          e.preventDefault()
          path = href
        }
      })
    }
  }
}