package clide.client

import clide.client.ui._

object Toasts extends Component {
  case class Toast(message: String)    
  
  private val toasts = TemplateVar[List[Toast]](List(
      Toast("Hallo"),
      Toast("Zweiter Toast")))
  
  val template: NodeFactory = toasts.map(list =>
    Div(id := "toasts")(list.map(toast => Div(className := "toast")(toast.message)) :_*)
  )
}