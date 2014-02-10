package clide.client

import clide.client.util._
import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._

object App extends JsApp("clide") {
  val counter = Observable.interval(10)
     
  val text = Subject("")
  
  val template = Div(Control.className := "clideApp")(
    Div(Control.id := "hallo")("Gib was ein: ", TextBox(TextBox.value <-- text, TextBox.value --(Event.once,TextBox.onInput)--> text)()),
    Div(Control.id := "hallo2", Control.title := "Hallo")("Ich zähle: ", "Noch ein Text"),
    Button(Button.onClick --> text.onNext("Hallo"))(text),
    new Dialog("Welcome to Clide", Query("username","martinring"), Query("password",""))
  )
}