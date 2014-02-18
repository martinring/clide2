package clide.client

import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._
import clide.client.ui.html.JsApp
import scala.collection.mutable.Buffer
import clide.client.ui.html.View

object App extends JsApp with History {
  val counter = Observable.interval(500)
  
  val text = Var("Test")
  val reset = Action (text := "Hallo") when text.map(_ != "Hallo")
    
  val username = Var("martinring")
     
  val view2 = 
    new Dialog("Hello, I am Google", Action(),
         Query("search for", username))
    
  val elems = ObservableBuffer.fromBuffer(clide.client.util.Buffer.apply("Das","war","schon","da"))
  
  var n = 0
  
  val addItem = Action {
    println(elems.length)
    elems.insert(elems.length / 2, "Hallo, ein Test " + n + " (" + (elems.length / 2) + ")")
    println(elems.length)
    n += 1
  }
  
  def obsBufView(name: String): NodeFactory = {
    var n = 1    
    val buf = ObservableBuffer.fromBuffer(clide.client.util.Buffer.empty[Int])    
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