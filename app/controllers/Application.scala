package controllers

import java.util.UUID
import scala.concurrent.duration.DurationInt
import scala.slick.driver.H2Driver.simple._
import akka.actor.ActorDSL._
import akka.actor.actorRef2Scala
import models.collab.Document
import models.collab.Operation
import models.collab.Server
import play.api.Play.current
import play.api.Routes
import play.api.db.slick.DB
import play.api.libs.concurrent.Akka
import play.api.libs.concurrent.Akka.system
import play.api.libs.iteratee._
import play.api.libs.json._
import play.api.mvc._
import akka.actor.ActorRef

object Application extends Controller with Secured {
  def index(path: String) = Action { implicit request =>
    def unauthorized = path match {
      case "login" => Ok(views.html.index(path)).withNewSession
      case _ => Redirect("/login").withNewSession
    }
    request.session.get("session") match {
      case None => unauthorized
      case Some(session) => DB.withSession { implicit dbsession =>
        val q = for (user <- models.Users if user.session === session)
          yield user.*
        q.firstOption match {
          case None => unauthorized
          case Some(u) =>
            if (path.isEmpty) Redirect(f"/${u.name}/backstage")            
            else Ok(views.html.index(path))           
        }
      }
    }    
  }
  
  def session = WebSocket.async[String] { request =>
    null
  }
  

  
  import models.collab.{Server,Document,Operation}
      
  val servers = scala.collection.mutable.Map[String,ActorRef]()
  
  //val server = 
  
  var id = 0
  
  def collab(path: String) = WebSocket.using[JsValue] { implicit request =>    
    val server = servers.getOrElseUpdate(path,Akka.system.actorOf(Server.props(Document(""))))
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

  // -- Javascript routing
  def javascriptRoutes = Action { implicit request =>
    import routes.javascript._
    Ok(
      Routes.javascriptRouter("jsRoutes")(
        routes.javascript.Application.index,        
        routes.javascript.Application.collab,
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