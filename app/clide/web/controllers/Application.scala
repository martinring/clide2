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
import scala.concurrent.Future

object Application extends Controller with UserRequests {
  import Messages._
  import Events._
  
  def index(path: String) = UserRequest.async { implicit request =>
    def notLoggedIn: SimpleResult = path match {
      case "login" => Ok(clide.web.views.html.index()).withNewSession
      case _       => Redirect("/login").withNewSession
    }
    request.ask(Validate).map {
      case Validated(info) =>
        if (path.isEmpty()) Redirect(s"${info.name}/backstage")
        else Ok(clide.web.views.html.index())
      case _               => notLoggedIn
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
        routes.javascript.Projects.session
      )
    ).as("text/javascript") 
  }

}