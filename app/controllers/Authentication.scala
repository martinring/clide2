package controllers

import play.api.mvc.{Controller,Action}
import scala.slick.driver.H2Driver.simple._
import play.api.Play.current
import play.api.db.slick.DB
import play.api.data.Form
import play.api.data.Forms._
import play.api.libs.json._
import play.api.libs.Crypto
import java.util.UUID

object Authentication extends Controller with Secured {
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
       DB.withSession { implicit session => !models.Users.getByName(name).firstOption.isDefined }),
      "email" -> email.verifying("email is already registered", email =>
       DB.withSession { implicit session => !models.Users.getByEmail(email).firstOption.isDefined }),
      "password" -> text(minLength=8)
    )
  )

  /**
   * Handle login form submission.
   */
  def login = Action(parse.json) { implicit request =>
    loginForm.bind(request.body).fold(        
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      { case (name,password) => DB.withSession { implicit session =>                 
        models.Users.getByName(name).firstOption match {
          case None => Status(401)(Json.obj("username" -> Json.arr("we don't know anybody with that username")))
          case Some(user) if (user.password != Crypto.sign(name+password)) => 
            Status(401)(Json.obj("password" -> Json.arr("invalid password")))            
          case Some(user) => 
            val sessionKey = Crypto.sign(UUID.randomUUID().toString() + System.nanoTime())                       
            val u = user.copy(session = Some(sessionKey))
            models.Users.getByName(name).update(u)
            Ok(Json.obj(
                "username" -> u.name, 
                "email" -> u.email)).withSession("session" -> sessionKey)            
    } } })               
  }
  
  def signup = Action(parse.json) { implicit request =>
    signupForm.bind(request.body).fold(
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      user => DB.withSession { implicit session =>        
        if (models.Users.insert(models.User(user._1, user._2, Crypto.sign(user._1 + user._3),None,None)) > 0)
          Ok(user._1)
        else
          BadRequest("Signup failed")
      }      
    ) 
  }  
  
  def validateSession = Authenticated { user => request =>
    Ok(Json.obj("username" -> user.name, "email" -> user.email))	       
  }
  
  def logout = Authenticated { user => request => 
    DB.withSession { implicit session: Session =>
      models.Users.getByName(user.name).update(user.copy(session = None))
    }
    Ok.withNewSession
  }
}