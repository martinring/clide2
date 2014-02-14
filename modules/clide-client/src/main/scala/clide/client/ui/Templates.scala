package clide.client.ui

import clide.client.ui.html._

object Templates {
  def dialog(content: NodeFactory): NodeFactory =
    Div(className := "dialogOuterContainer")(
      Div(className := "dialogInnerContainer")(
        Div(className := "dialog")(
          content
        )
      )
    )

  def container(content: NodeFactory): NodeFactory = 
    Div(className := "container")(content)

  def row(content: NodeFactory): NodeFactory =
    Div(className := "row")(content)    

  def twoColumns(left: NodeFactory, right: NodeFactory): NodeFactory =
    Seq(Div(className := "col-sm-5 col-sm-offset-1 col-lg-4 col-lg-offset-2")(left),
        Div(className := "col-sm-5 col-lg-4")(right))

  def oneColumn(content: NodeFactory): NodeFactory = 
    Div(className := "col-sm-10 col-sm-offset-1 col-lg-8 col-lg-offset-2 text-right")(content)
    
  def pullRight(content: NodeFactory): NodeFactory =
    Div(className := "pull-right")(content)

  object Forms {
    def text(descr: String, v: Var[String]): NodeFactory =
      Div(className := "form-group")(
        TextBox(className := "form-control", placeholder := descr, value := v.get, value <-> v, input updates v)()
      )
      
    def password(descr: String, v: Var[String]): NodeFactory =
      Div(className := "form-group")(
        TextBox(className := "form-control", inputType := "password", placeholder := descr, value := v.get, value <-> v, input updates v)()
      )
      
    def checkbox(descr: String, v: Var[Boolean]): NodeFactory = {
      Label(labelFor := "descr", click updates v)(
        CheckBox(name := descr, checked := v.get, checked <-> v)(),
        Span()(" " + descr)
      )
    }
  }
}