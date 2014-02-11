package clide.client.ui

import clide.client.ui.html._
import clide.client.rx.Subject

case class Query[T](name: String, default: T) {
  val value = Var(default)
}

class Dialog(title: String, submit: Action, queries: Query[String]*) extends UserControl {
  val reset = Action {
    queries.foreach(q => q.value := q.default)
  }
  
  val template = Div(className := "dialog")(
    H1()(title),
    queries.map { q =>
      Div(className := "form-group")(
        Span()(q.name + ":"),
        TextBox(value <-> q.value, input updates q.value)()
      )
    },
    Button(click triggers reset)("reset"),
    Button(submit)("ok")
  )
}