package controllers

import play.api._
import play.api.mvc._
import play.api.data._
import play.api.data.Forms._

object Application extends Controller with Secured {
  def index = Action { implicit request =>
    Ok(views.html.index("/"))
  }

  def any(path: String) = Action { implicit request =>
    Ok(views.html.index(path))
  }  
  
  def session = WebSocket.async[String] { request =>
    null
  }
  
  // -- Authentication
  val loginForm = Form(
    tuple(
      "name" -> text,
      "password" -> text
    ) verifying ("Invalid name or password", result => result match {
      case (name, password) => true //User.authenticate(email, password).isDefined
    })
  )
  
  val signupForm = Form(
    tuple(
      "name" -> text,
      "email" -> text,
      "password" -> text
    ) verifying ()
  )

  /**
   * Handle login form submission.
   */
  def authenticate = Action { implicit request =>
    loginForm.bindFromRequest.fold(
      formWithErrors => BadRequest("forbidden"),
      user => Redirect(routes.Application.index).withSession("email" -> user._1)
    )
  }

  /**
   * Logout and clean the session.
   */
  def logout = Action {
    Redirect(routes.Application.index).withNewSession.flashing(
      "success" -> "You've been logged out"
    )
  }

  // -- Javascript routing
  def javascriptRoutes = Action { implicit request =>
    import routes.javascript._
    Ok(
      Routes.javascriptRouter("jsRoutes")(
        routes.javascript.Application.index   
      )
    ).as("text/javascript") 
  }

}