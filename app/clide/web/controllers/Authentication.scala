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
import play.api.libs.concurrent.Execution.Implicits.defaultContext

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
       DB.withSession { implicit session => !UserInfos.getByName(name).firstOption.isDefined }),
      "email" -> email.verifying("email is already registered", email =>
       DB.withSession { implicit session => !UserInfos.getByEmail(email).firstOption.isDefined }),
      "password" -> text(minLength=8)
    )
  )

  /**
   * Handle login form submission.
   */
  def login = Action.async(parse.json) { implicit request => Future {
    loginForm.bind(request.body).fold(
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      { case (name,password) => DB.withSession { implicit session =>                 
        UserInfos.getByName(name).firstOption match {
          case None => Status(401)(Json.obj("username" -> Json.arr("we don't know anybody with that username")))
          case Some(user) if (user.password != Crypto.sign(name+password)) => 
            Status(401)(Json.obj("password" -> Json.arr("invalid password")))            
          case Some(user) =>            
            val sessionKey = Crypto.sign(UUID.randomUUID().toString() + System.nanoTime())                       
            val u = user.copy(session = Some(sessionKey))
            UserInfos.getByName(name).update(u)
            Ok(Json.obj(
                "username" -> u.name, 
                "email" -> u.email)).withSession("session" -> sessionKey)            
  } } } ) } }
  
  
  def signup = Action(parse.json) { implicit request =>
    signupForm.bind(request.body).fold(
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      user => DB.withSession { implicit session =>
        val u = UserInfo(user._1,user._2,Crypto.sign(user._1+user._3),None,None)
        if (UserInfos.insert(u) > 0) {
          clide.actors.Server.instance ! clide.actors.Users.SignedUp(u)
          Ok(user._1) 
        }          
        else
          BadRequest("Signup failed")
      }      
    ) 
  }
  
  def validateSession = Authenticated { request =>
    Ok(Json.obj("username" -> request.user.name, "email" -> request.user.email))	       
  }
  
  def logout = Authenticated { request => 
    DB.withSession { implicit session: Session =>
      UserInfos.getByName(request.user.name).update(request.user.copy(session = None))
    }
    Ok.withNewSession
  }
}