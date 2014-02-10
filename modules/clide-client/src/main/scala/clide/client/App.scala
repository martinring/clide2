package clide.client

import clide.client.util._
import clide.client.ui.html._
import clide.client.rx._

object App extends JsApp("clide") {
  val counter = Observable.interval(10)
     
  val text = Subject("Hallo")
  
  val template = Div(Control.className := "test")(
    Div(Control.id := "hallo")(
      "Gib was ein: ", 
      TextBox(TextBox.value := text.get, TextBox.value --(TextBox.onInput)--> text)()),
    Div(Control.id := "hallo2", Control.title := "Hallo")(
      "Ich zähle: ",
    "Noch ein Text",
    Button(Control.title := "hallo")(
      "klick mich")
    ), text
  )
}