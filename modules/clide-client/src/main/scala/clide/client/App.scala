package clide.client

import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._
import clide.client.ui.html.JsApp

object App extends JsApp with Routing {
  val counter = Observable.interval(500)
     
  val text = Var("Test")
  
  counter.foreach(_ => text.update())
  
  val reset = Action (text := "Hallo") when text.map(_ != "Hallo")
  
  val username = Var("martinring")
  
  val view1 = {
    val password = Var("")
    val password2 = Var("")
    
    val valid = for {
      username <- username
      password <- password
      password2 <- password2
    } yield password.length >= 8 &&
            password == password2 &&
            username.length >= 8

    new Dialog("Welcome to Clide", Action(Location.path = "/"+username.get+"/"+password.get) when valid, 
        Query("username", username), 
        Query("password", password), 
        Query("repeat password", password2))
  }
  
  val view2 = {
    val password = Var("")
    val password2 = Var("")
    
    val valid = for {
      username <- username
      password <- password
      password2 <- password2
    } yield password.length >= 8 &&
            password == password2 &&
            username.length >= 8

    new Dialog("* Welcome to Clide *", Action(Location.path = "/"+username.get+"/"+password.get) when valid, 
        Query("username", username), 
        Query("password", password), 
        Query("repeat password", password2))
  }
  
  val login = Observable.interval(2000).map { count =>
    if (count % 2 == 0) view1 else view2
  }
  
  val template = Div(className := "clideApp")(
    "Wir befinden uns hier: ", Location.path, text,
    Div(id := "hallo")("Gib was ein: ", TextBox(value <-> text, input updates text)()),
    Div(id := "link")(Link(reset, href := "#")("reset")),
    Div(id := "hallo2", title := "Hallo")("Ich zähle: ", counter.map(_.toString)),
    Button(reset)("Hallo"),Link(href := "google.com")("Ein Link"),
    login
  )
}