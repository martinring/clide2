package clide.web.controllers

import java.util.UUID
import scala.concurrent.duration.DurationInt
import scala.slick.driver.H2Driver.simple._
import akka.actor.ActorDSL._
import akka.actor.actorRef2Scala
import play.api.Play
import play.api.Play.current
import play.api.Routes
import play.api.db.slick.DB
import play.api.libs.concurrent.Akka
import play.api.libs.concurrent.Akka.system
import play.api.libs.iteratee._
import play.api.libs.json._
import play.api.mvc._
import akka.actor.ActorRef
import clide.models._
import clide.actors._
import clide.actors.Infrastructure._
import clide.actors.users.UserActor
import clide.actors.UserServer._
import scala.concurrent.Future
import akka.pattern.Patterns._
import akka.util.Timeout

object Application extends Controller with Secured {
  def index(path: String) = Action.async { implicit request =>
    def default = path match {
      case "login" => Ok(clide.web.views.html.index()).withNewSession
      case _       => Redirect("/login").withNewSession
    }
    val session = for {
      name <- request.session.get("user")
      key  <- request.session.get("key")
    } yield (name,key)    
    session match {
      case None => Future.successful(default)
      case Some((name,key)) =>
        implicit val context = Akka.system.dispatcher
        val timeout = Timeout(5 seconds)
        val future = (ask(server, WithUser(name,UserActor.Validate(key)),timeout)).mapTo[UserEvent]
        future.map {
          case Validated(user) => Ok(clide.web.views.html.index())
          case _               => default
        }
    }
  }  
  
  // -- Javascript routing
  def javascriptRoutes = Action { implicit request =>
import routes.javascript._
    Ok(
      Routes.javascriptRouter("jsRoutes")(
        routes.javascript.Application.index,      
        routes.javascript.Authentication.login,
        routes.javascript.Authentication.logout,   
        routes.javascript.Authentication.validateSession,
        routes.javascript.Authentication.signup,
        routes.javascript.Projects.index,        
        routes.javascript.Projects.put,
        routes.javascript.Projects.delete,
        routes.javascript.Projects.session,
        routes.javascript.Files.getTree,
        routes.javascript.Files.newFile,
        routes.javascript.Files.deleteFile
      )
    ).as("text/javascript") 
  }

}