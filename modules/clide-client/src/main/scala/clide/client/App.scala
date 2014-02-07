package clide.client

import clide.client.util._
import clide.client.ui._
import clide.client.rx.ObservableCollection
import org.scalajs.dom._
import clide.client.rx.Observable
import scala.concurrent.duration._
import scala.language.postfixOps

object App extends JsApp("clide") {
  val counter = Observable.interval(10)
  
   
  val text = TemplateVar("Hallo")
  
  val template = Div(className := "test")(
    Div(id := "hallo")(
      "Gib was ein: ", 
      TextBox(value --> text)()),
    Div(id := "hallo2", title <-- counter.map(_ * 2).map(_.toString))(
      "Ich zähle: ", 
      counter.map(x => x * x).map(_.toString)),
    "Noch ein Text",
    Button(title := "hallo")(
      "klick mich ", 
      text.map(_.reverse)), Toasts
  )
}