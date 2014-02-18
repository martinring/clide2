package clide.client.ui

import clide.client.ui.html._
import clide.client.rx.Subject
import clide.client.ui.html.View

case class Query[T](name: String, value: Var[T])

class Dialog(title: String, submit: Action, queries: Query[String]*) extends View {
  val reset = Action {
    queries.foreach(q => q.value.reset())
  }
  
  val template = Div(className := "dialog")(
    Heading(1)()(title),
    queries.map { q =>
      Div(className := "form-group")(
        Span()(q.name + ":"),
        TextBox(value := q.value.get, value <-> q.value, input updates q.value)()
      )
    },
    Button(reset)("reset"),
    Button(submit)("ok")
  )
}