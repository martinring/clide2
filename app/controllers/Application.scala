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
import scala.slick.driver.BasicProfile._
import scala.slick.driver.H2Driver.simple._
import play.api.libs.json.JsString
import play.api.libs.concurrent.Execution.Implicits._
import play.api.libs.concurrent.Akka
import play.api.libs.concurrent.Akka.system
import play.api.Play.current
import play.api.libs.json.Json
import play.api.libs.Crypto
import views.html.defaultpages.badRequest
import java.util.UUID
import views.html.defaultpages.unauthorized

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
    ) 
  )
  
  // -- Signup
  val signupForm = Form(
    tuple(
      "username" -> text.verifying("name is already in use", name => 
        !Seq("login","logout","signup","assets").contains(name) &&
        withSession { implicit session => !models.Users.getByName(name).firstOption.isDefined }),
      "email" -> email.verifying("email is already registered", email =>
        withSession { implicit session => !models.Users.getByEmail(email).firstOption.isDefined }),
      "password" -> text(minLength=8)
    )
  )

  /**
   * Handle login form submission.
   */
  def login = Action(parse.json) { implicit request =>    
    loginForm.bind(request.body).fold(        
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      { case (name,password) => withSession { implicit session =>                 
        models.Users.getByName(name).firstOption match {
          case None => Status(401)(Json.obj("username" -> Json.arr("we don't know anybody with that username")))
          case Some(user) if (user.password != Crypto.sign(name+password)) => 
            Status(401)(Json.obj("password" -> Json.arr("invalid password")))            
          case Some(user) => 
            val sessionKey = UUID.randomUUID().toString()
            val u = user.copy(session = Some(sessionKey))
            models.Users.getByName(name).update(u)
            Ok(Json.obj("username" -> u.name, "email" -> u.email, "session" -> u.session, "gravatar" -> u.gravatar))
    } } })               
  }
  
  def validateSession = Action(parse.json) { implicit request =>    
    val session = (request.body \ "session").as[Option[String]]
    val q = for (user <- models.Users if user.session === session)
      yield user.*
    withSession { implicit session =>
      q.firstOption match {
        case Some(u) => Ok(Json.obj("username" -> u.name, "email" -> u.email, "session" -> u.session, "gravatar" -> u.gravatar))
        case None => BadRequest("Invalid session")
      }
    }        
  }
  
  def signup = Action(parse.json) { implicit request =>
    signupForm.bind(request.body).fold(
      formWithErrors => BadRequest(formWithErrors.errorsAsJson),
      user => withSession { implicit session =>        
        if (models.Users.insert(models.User(user._1, user._2, Crypto.sign(user._1 + user._3),None,None)) > 0)
          Ok(user._1)
        else
          BadRequest("Signup failed")
      }      
    ) 
  }
  
  import models.collab.{Server,Document,Operation}
  
  val server = Akka.system.actorOf(Server.props(Document("Test")),"collab_demo_doc_server")
  
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
	          server ! Server.Change(rev,op)
            case "register" =>                            
              server ! Server.Register("client"+id)
          }
        case Server.Initialize(rev, doc) =>          
          channel.push(Json.obj(
            "type" -> "init",
            "rev" -> rev,
            "doc" -> doc.content))
        case Server.Acknowledgement => 
          channel.push(Json.obj(
            "type" -> "ack"))
        case Server.Change(rev,op) =>
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
   * Logout and clean the session.
   TODO!
  def logout = Action { withSession =>
    
  }*/

  // -- Javascript routing
  def javascriptRoutes = Action { implicit request =>
    import routes.javascript._
    Ok(
      Routes.javascriptRouter("jsRoutes")(
        routes.javascript.Application.index,        
        routes.javascript.Application.login,        
        routes.javascript.Application.validateSession,
        routes.javascript.Application.signup,
        routes.javascript.Application.collab,
        routes.javascript.Projects.index
      )
    ).as("text/javascript") 
  }

}