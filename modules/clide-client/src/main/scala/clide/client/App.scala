package clide.client

import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._
import clide.client.ui.html.JsApp
import scala.collection.mutable.Buffer

object Auth {
  val username = Var("martinring")
} 

object Login extends View {
  val password  = Var("") 
  val password2 = Var("")
    
  val valid = for {
    username <- Auth.username
    password <- password
    password2 <- password2
  } yield password.length >= 8 &&
          password == password2 &&
          username.length >= 8
            
  val template = new Dialog("Welcome to Clide", Action(App.Location.path = "/"+Auth.username.get+"/"+password.get) when valid, 
        Query("username", Auth.username), 
        Query("password", password), 
        Query("repeat password", password2))
}

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
  
  val template = Div(className := "clideApp")(
    "Wir befinden uns hier: ", Location.path, text,
    Div(id := "hallo")("Gib was ein: ", TextBox(value <-> text, input updates text)()),
    Div(id := "link")(Link(reset)("reset")),
    Div(id := "hallo2", title := "Hallo")("Ich zähle: ", counter.map(_.toString)),
    Button(reset)("Hallo"),Link(href := "/google.com")("Ein Link"),
    Link(href := "http://www.google.com")("Externer Link"),
    Location.path.map({
      case "/google.com" => view2
      case _ => Login
    }).varying,
    H1()("Eine Liste:"),
    Button(click triggers addItem)("hinzufügen"),
    elems.observable.mapChanges { str => 
      Div(click triggers Action(elems -= str))(str)  
    }
  )
}