package clide.web.controllers

import play.api.mvc.{Controller,Action}
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import play.api.data.Form
import play.api.data.Forms._
import play.api.libs.json._
import play.api.libs.Crypto
import java.util.UUID
import clide.models._
import scala.concurrent.Future
import clide.actors.Messages._
import clide.actors.Events._
import play.api.mvc.Results
import play.Logger

object Authentication extends Controller with Secured with ActorAsk {
  // -- Authentication
  val loginForm = Form(
    tuple(
      "username" -> text,
      "password" -> text
    ) 
  )
  
  // -- Signup
  val signupForm = Form(
    tuple(
      "username" -> text.verifying("name is already in use", name => 
        !Seq("login","logout","signup","assets").contains(name) &&
       DB.withSession { implicit session => !UserInfos.getByName(name).firstOption.isDefined }),
      "email" -> email.verifying("email is already registered", email =>
       DB.withSession { implicit session => !UserInfos.getByEmail(email).firstOption.isDefined }),
      "password" -> text(minLength=8)
    )
  )

  /**
   * Handle login form submission.
   */
  def login = Action.async(parse.json) { implicit request =>
    loginForm.bind(request.body).fold(
      formWithErrors => Future.successful(BadRequest(formWithErrors.errorsAsJson)),
      { case (name,password) =>
        (server ? WithUser(name,Login(password))).collect {
          case LoggedIn(user,login) => 
            Ok(Json.obj(
                "username" -> user.name, 
                "email" -> user.email)
            ).withSession(
                "user" -> login.user,
                "key"  -> login.key
            )
          case DoesntExist(name) =>
            Status(401)(Json.obj("username" -> Json.arr("we don't know anybody by that name")))
          case WrongPassword(user) =>
            Status(401)(Json.obj("password" -> Json.arr("invalid password")))
          case other =>
            Status(500)(other.toString)
        }
    })
  }
  
  def signup = Action.async(parse.json) { implicit request =>
    signupForm.bind(request.body).fold(
      formWithErrors => Future.successful(BadRequest(formWithErrors.errorsAsJson)),
      { case (name,email,password) =>
        (server ? SignUp(name,email,password)).collect {        
          case SignedUp(user) =>
            Ok("Your account has been created. Have fun!")          
        }
      })
  }
  
  def validateSession = Authenticated { request =>    
    Ok(Json.obj("username" -> request.user.name, 
                "email" -> request.user.email))
  }
  
  def logout = Action.async { implicit request =>
    sessionInfo match {
      case None => Future.successful(Results.Unauthorized)
      case Some((name,key)) =>
        (server ? WithUser(name,Logout(key))).collect {
	      case NotLoggedIn => Results.Unauthorized
	      case LoggedOut   => Results.Ok.withNewSession
	    }
    }
  }
}