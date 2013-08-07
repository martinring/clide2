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
import play.api.libs.concurrent.Akka
import play.api.libs.concurrent.Akka.system
import play.api.Play.current
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
    
  def collab = WebSocket.using[JsValue] { implicit request =>
    implicit val sys = system
    implicit val timeout = 5 seconds
    val (out,channel) = Concurrent.broadcast[JsValue]
    val in = Iteratee.foreach[JsValue]{ println }        
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