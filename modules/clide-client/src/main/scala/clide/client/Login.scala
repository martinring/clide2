package clide.client

import clide.client.ui.html._
import clide.client.ui._

object Auth {
  val username = "martinring"
} 

class LoginView extends View {
  val username     = Var(Auth.username)
  val password     = Var("")
  val staySignedIn = Var(true)

  import Templates._
  
  val login = Action(App.Location.path = "/whatever")
  
  val leftColumn: NodeFactory = Seq(
    Heading(2)()("Welcome to clide"),
    Paragraph()("Please enter your credentials"),
    Form()(
      Forms.text("username",username),
      Forms.password("password",password),
      Forms.checkbox("keep me signed in", staySignedIn),
      pullRight(Seq(
        Link(className := "btn btn-link")("Sign Up"),
        Button(className := "btn btn-primary", buttonType := "submit", login)("Login")
      ))
    )
  )
  val rightColumn: NodeFactory = Div(className := "banner text-justify")(    
    Heading(2)()("What is this?"),
    Paragraph()("Clide is a language agnostic, collaborative IDE running in the cloud at your service."),
    Paragraph()("It is developed and maintained by ",
                Link(href := "http://github.com/martinring")("Martin Ring")," at the ",
                Link(href := "http://www.dfki.de/cps")("German Research Center for Artificial Intelligence (DFKI)"),
                " in Bremen, Germany."),
    Paragraph()("If you want to know what is running under the hood or want to contribute to the project, feel free to explore the ",
                Link(href := "http://github.com/martinring/clide2")("github project")," or get in touch with us.")
  )
  
  val template = dialog(container(Seq(
    row(twoColumns(leftColumn, rightColumn)),
    row(oneColumn(Small(className := "text-muted")("© 2012-2013 Martin Ring - Licensed under LGPL v3 - You're looking at version 2.0-SNAPSHOT. Last updated 2/1/2014."))) 
  )))
}