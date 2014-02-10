package clide.client.ui

import clide.client.ui.html._
import clide.client.rx.Subject

case class Query[T](name: String, default: T) {
  val value = Subject(default)
}

class Dialog(title: String, queries: Query[String]*) extends UserControl {
  
  
  val template = Div(Control.className := "dialog")(
    H1()(title),
    queries.map { q =>
      Div(Control.className := "form-group")(
        Span()(q.name + ":"),
        TextBox(TextBox.value := q.default, TextBox.value --(TextBox.onInput)--> q.value)()
      )
    }
  )
}