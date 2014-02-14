package clide.client

import clide.client.ui.html._
import clide.client.rx._
import clide.client.ui._
import clide.client.ui.html.JsApp
import scala.collection.mutable.Buffer
import clide.client.ui.html.View

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

object App extends JsApp with History {
  val counter = Observable.interval(500)
  val text = Var("Test")
  val reset = Action (text := "Hallo") when text.map(_ != "Hallo")
  val username = Var("martinring")
     
  val view2 = 
    new Dialog("Hello, I am Google", Action(),
         Query("search for", username))
    
  val elems = ObservableBuffer.fromBuffer(clide.client.util.Buffer.apply("Das","war","schon","da"))
  
  var n = 0
  val addItem = Action {
    println(elems.length)
    elems.insert(elems.length / 2, "Hallo, ein Test " + n + " (" + (elems.length / 2) + ")")
    println(elems.length)
    n += 1
  }
  
  def obsBufView(name: String): NodeFactory = {
    var n = 1    
    val buf = ObservableBuffer.fromBuffer(clide.client.util.Buffer.empty[Int])    
    val add = Action {
      buf += n
      n += 1
    }
    Span(className := "obs")(
      Span()(name), Button(click triggers add)("+"),
      OrderedList()(
        buf.observable.mapChanges { i => ListItem()(Button(click triggers Action(buf -= i))("x"), obsBufView(name + "." + i)) }
      )
    )             
  }
  
  val template = Div(className := "clideApp")(
    "Wir befinden uns hier: ", Location.path, text,
    Div(id := "hallo")("Gib was ein: ", TextBox(value <-> text, input updates text)()),
    Div(id := "link")(Link(reset)("reset")),
    Div(id := "hallo2", title := "Hallo")("Ich zähle: ", counter.map(_.toString)),
    Button(reset)("Hallo"),Link(href := "/google.com")("Ein Link"),
    Link(href := "http://www.google.com")("Externer Link"),
    Location.path.map({
      case "/login" => new LoginView
      case "/google.com" => view2 
      case _ => Seq() : NodeFactory
    }).varying,
    Link(href := "/login")("login"),
    Heading(2)()("Eine Liste:"),    
    PreFormated()("""def obsBufView(name: String): NodeFactory = {
  var n = 1    
  val buf = ObservableBuffer.fromBuffer(clide.client.util.Buffer.empty[Int])    
  val add = Action {
    buf += n
    n += 1
  }
  Span(className := "obs")(
    Span()(name), Button(click triggers add)("+"),
    OrderedList()(
      buf.observable.mapChanges { i => ListItem()(Button(click triggers Action(buf -= i))("x"), obsBufView(name + "." + i)) }
    )
  )
}"""),  
    obsBufView("0")
  )
}