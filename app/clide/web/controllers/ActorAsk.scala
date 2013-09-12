package clide.web.controllers

import akka.util.Timeout
import scala.concurrent.duration._
import play.api.mvc.Controller
import akka.actor.ActorRef
import play.api.Play.current

trait ActorAsk { this: Controller =>
  implicit val timeout = Timeout(1 second)
  implicit def ask(act: ActorRef) = akka.pattern.ask(act)
  implicit val executionContext = play.api.libs.concurrent.Akka.system.dispatcher
  val server = clide.actors.Infrastructure.server 
}