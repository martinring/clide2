package clide.client.ui.html

import org.scalajs.dom._
import clide.client.rx._
import scala.scalajs.js

trait History extends JsApp {
  override def delayedInit(body: => Unit): Unit = super.delayedInit{
    Location.init()
    body
  }
  
  object Location {
    def back() = window.history.back()
    def forward() = window.history.forward()
    def path: Observable[String] = loc.startWith(window.location.pathname.asInstanceOf[String]).varying
    def path_=(path: String) = if (path != window.location.pathname) {     
      loc.onNext(path)
      window.history.pushState(null, path, path)
    } 
    
    private val loc = Subject.empty[String]
    
    private[History] def init() {
      // We watch all popstate events just to update the current location
      Observable.fromEvent[PopStateEvent](window, "popstate")
        .foreach { _ => loc.onNext(window.location.pathname) }
      // We need to intercept all button clicks to prevent submit actions
      Mouse.click.filter(me => me.srcElement.nodeName.toLowerCase() == "button")
        .foreach { me => me.preventDefault() }
      // We also need to intercept clicked links to prevent navigating off the page
      Mouse.click.filter(me => !me.ctrlKey && !me.metaKey && me.button != 2)
        .filter(me => me.srcElement.nodeName.toLowerCase() == "a")
        .foreach { me =>            
          val href = me.srcElement.getAttribute("href")                    
          if (href != null && href.startsWith("/")) {
            me.preventDefault()
            path = href
          }
        }
    }
  }
}