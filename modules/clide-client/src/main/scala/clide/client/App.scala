package clide.client

import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._
import clide.client.ui.html.JsApp
import scala.collection.mutable.Buffer
import clide.client.ui.html.View
import clide.reactive.Event
import scala.concurrent.Promise
import org.scalajs.dom.EventTarget
import org.scalajs.dom.MouseEvent
import org.scalajs.dom.window
import org.scalajs.dom.KeyboardEvent
import scala.scalajs.js.annotation.JSExport

@JSExport
object App extends JsApp with History {
  val counter = Observable.interval(500)
  
  val text = Var("Test")
  val reset = Action (text := "Hallo") when text.map(_ != "Hallo")
    
  val username = Var("martinring")
     
  val view2 = 
    new Dialog("Hello, I am Google", Action(),
         Query("search for", username))
    
  val elems = ObservableBuffer.fromBuffer(Buffer.apply("Das","war","schon","da"))    
  
  var n = 0
  
  implicit val ec = scala.scalajs.concurrent.JSExecutionContext.runNow 
      
  def domEvent[E](target: EventTarget, name: String): Event[E] = Event.fromCallback[E] { handler =>
    val listener: org.scalajs.dom.Event => Unit = ( event => handler(event.asInstanceOf[E]) )
    val jsListener: scalajs.js.Function1[org.scalajs.dom.Event,Unit] = listener
    println("gerister " + name)
    target.addEventListener(name, jsListener)
    () => {  
      println("remove " + name)
      target.removeEventListener(name, jsListener)
    }
  }      
    
  def mousedown: Event[(Int,Int)] = domEvent[MouseEvent](window,"mousedown").map(e => (e.clientX.toInt, e.clientY.toInt))
  def mouseup:   Event[(Int,Int)] = domEvent[MouseEvent](window,"mouseup").map(e => (e.clientX.toInt, e.clientY.toInt))
  def mousemove: Event[(Int,Int)] = domEvent[MouseEvent](window,"mousemove").map(e => (e.clientX.toInt, e.clientY.toInt))
  def mouseout:  Event[Unit]      = domEvent[MouseEvent](window,"mouseout").map(e => ())
  
  
  def keypress: Event[Char] = domEvent[KeyboardEvent](window, "keypress").map(e => scalajs.js.String.fromCharCode(e.keyCode).head)
  
  def diff(p0: (Int,Int),pn: (Int,Int)): (Int,Int) = (pn._1 - p0._1, pn._2 - p0._2) 
  def add(p1: (Int,Int), p2: (Int,Int)): (Int,Int) = (p1._1 + p2._1, p1._2 + p2._2) 
  
  def drags = for {
    (x0,y0) <- mousedown
    (x1,y1) <- mousemove until mouseup.head    
  } yield (x1-x0, y1-y0)
  
  (drags until keypress.contains('x')).foreach(println)
  
  val addItem = Action {
    println(elems.length)
    elems.insert(elems.length / 2, "Hallo, ein Test " + n + " (" + (elems.length / 2) + ")")
    println(elems.length)
    n += 1
  }
  
  def obsBufView(name: String): NodeFactory = {
    var n = 1    
    val buf = ObservableBuffer.fromBuffer(Buffer.empty[Int])    
    val add = Action { buf += n; n += 1 }
    Span(className := "obs")(
      Span()(name), Button(click triggers add)("+"),
      OrderedList()(
        buf.observable.mapChanges { i => 
          ListItem()(Button(click triggers Action(buf -= i))("x"), obsBufView(name + "." + i)) 
        }
      )
    )             
  }
  
  val template = Div(className := "clideApp")(
    "Wir befinden uns hier: ", Location.path, 
    Div()(text.map(_.reverse.toUpperCase)),
    Div(id := "hallo")("Gib was ein: ", TextBox(value <-> text, input updates text)()),
    Div(id := "link")(Link(reset)("reset")),
    Div(id := "hallo2", title := "Hallo")("Ich zähle: ", counter.map(_.toString)),
    Button(reset)("Hallo"),Link(href := "/google.com")("Ein Link"),
    Link(href := "http://www.google.com")("Externer Link"),
    Location.path.map({
      case "/login" => new LoginView
      case "/google.com" => view2 
      case _ => Seq() : NodeFactory
    }),
    Link(href := "/login")("login"),
    Heading(2)()("Eine Liste:"),    
    obsBufView("0")
  )
}