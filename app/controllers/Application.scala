package controllers

import play.api._
import play.api.Play.current
import play.api.mvc._
import play.api.data._
import play.api.data.Forms._
import play.api.db.slick.DB.withSession
import play.api.libs.json.JsValue
import play.api.libs.iteratee.Concurrent
import play.api.libs.iteratee.Iteratee
import akka.actor.Actor
import akka.actor.Props
import akka.actor.ActorDSL._
import scala.concurrent.duration._
import play.api.libs.json.JsString
import play.api.libs.concurrent.Execution.Implicits._
import models.ot.{Document,Server,Operation,Change}
import play.api.libs.concurrent.Akka
import play.api.libs.concurrent.Akka.system
import models.ot.Acknowledgement
import play.api.Play.current
import models.ot.Register
import models.ot.Initialize
import play.api.libs.json.Json

object Application extends Controller with Secured {
  def index(path: String) = Action { implicit request =>    
    Ok(views.html.index(path))
  }
  
  def session = WebSocket.async[String] { request =>
    null
  }
  
  // -- Authentication
  val loginForm = Form(
    tuple(
      "username" -> text,
      "password" -> text
    ) verifying ("Invalid name or password", result => result match {
      case (name, password) => name == "martinring" //User.authenticate(email, password).isDefined
    })
  )
  
  // -- Signup
  val signupForm = Form(
    tuple(
      "name" -> text.verifying("name is already taken", name => 
        !Seq("login","logout","signup","assets").contains(name) &&
        withSession { implicit session => !models.Users.getByName(name).firstOption.isDefined }),
      "email" -> email.verifying("email is already taken", email =>
        withSession { implicit session => !models.Users.getByEmail(email).firstOption.isDefined }),
      "password" -> text(minLength=8)
    )
  )

  /**
   * Handle login form submission.
   */
  def login = Action { implicit request =>
    loginForm.bindFromRequest.fold(
      formWithErrors => BadRequest("Invalid username or password"),
      user => Ok(f"you successfully logged in as '${user._1}'").withSession("name" -> user._1)
    )
  }
  
  val server = Akka.system.actorOf(Server.props(Document("Test")))
  var id = 0
  
  def collab = WebSocket.using[JsValue] { implicit request =>
    implicit val sys = system
    implicit val timeout = 5 seconds
    val (out,channel) = Concurrent.broadcast[JsValue]
    val client = actor(new Act {      
      id += 1
      become {
        case json: JsValue   =>
          (json \ "type").as[String] match {
            case "change" =>
              val rev = (json \ "rev").as[Int]
	          val op = (json \ "op").as[Operation]
	          server ! Change(rev,op)
            case "register" =>
              server ! Register("client"+id)
          }
        case Initialize(rev, doc) =>
          channel.push(Json.obj(
            "type" -> "init",
            "rev" -> rev,
            "doc" -> doc.content))
        case Acknowledgement => 
          channel.push(Json.obj(
            "type" -> "ack"))
        case Change(rev,op) =>
          channel.push(Json.obj(
            "type" -> "change",
            "rev" -> rev,
            "op" -> op))
        case e: Exception =>
          channel.push(Json.obj(
            "type" -> "error",
            "msg" -> e.getMessage(),
            "ss" -> e.getStackTraceString))
      }
    })
    val in = Iteratee.foreach[JsValue] { client ! _ }        
    (in,out)
  }
  
  /**
   * Handle signup form submission.
   */
  def signup = Action { implicit request =>
    signupForm.bindFromRequest.fold(
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      user => Ok(f"you successfully logged in as '${user._1}'").withSession("name" -> user._1)
    )
  }  

  /**
   * Logout and clean the session.
   */
  def logout = Action {
    Redirect(routes.Application.index("")).withNewSession.flashing(
      "success" -> "You've been logged out"
    )
  }

  // -- Javascript routing
  def javascriptRoutes = Action { implicit request =>
    import routes.javascript._
    Ok(
      Routes.javascriptRouter("jsRoutes")(
        routes.javascript.Application.index,   
        routes.javascript.Application.login,
        routes.javascript.Application.collab
      )
    ).as("text/javascript") 
  }

}