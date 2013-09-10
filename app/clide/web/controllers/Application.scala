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
import clide.models.Users

object Application extends Controller with Secured {
  def index(path: String) = Action { implicit request =>
    def unauthorized = path match {
      case "login" => Ok(clide.web.views.html.index()).withNewSession
      case _ => Redirect("/login").withNewSession
    }
    request.session.get("session") match {
      case None => unauthorized
      case Some(session) => DB.withSession { implicit dbsession =>
        val q = for (user <- Users if user.session === session)
          yield user.*
        q.firstOption match {
          case None => unauthorized
          case Some(u) =>
            if (path.isEmpty) Redirect(f"/${u.name}/backstage")            
            else Ok(clide.web.views.html.index())           
        }
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