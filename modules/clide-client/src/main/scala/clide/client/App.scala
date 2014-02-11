package clide.client

import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._
import clide.client.ui.html.JsApp

object App extends JsApp with Routing {
  val counter = Observable.interval(500)
     
  val text = Var("Test")    
  
  val reset = Action (text := "Hallo") when text.map(_ != "Hallo")    
  
  val login = {
    val username = Query("username","martinring")
    val password = Query("password","")
    val password2 = Query("repeat password","")
    
    val valid = for {
      username <- username.value
      password <- password.value
      password2 <- password2.value
    } yield password.length >= 8 && 
            password == password2 &&
            username.length >= 8

    new Dialog("Welcome to Clide", Action(Location.path = "/"+username.value.get+"/"+password.value.get) when valid, username, password, password2)
  }
  
  val template = Div(className := "clideApp")(
    "Wir befinden uns hier: ", Location.path,
    Div(id := "hallo")("Gib was ein: ", TextBox(value <-> text, input updates text)()),
    Div(id := "link")(Link(reset, href := "#")("reset")),
    Div(id := "hallo2", title := "Hallo")("Ich zähle: ", counter.map(_.toString)),
    Button(reset)("Hallo"),Link(href := "google.com")("Ein Link"),
    login
  )
}