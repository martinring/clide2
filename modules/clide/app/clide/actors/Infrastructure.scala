package clide.actors

import play.api.Play.current
import akka.actor._
import com.typesafe.config.ConfigFactory

object Infrastructure {
  var server: Option[ActorRef] = None
  private var system: Option[ActorSystem] = None
  
  def initialize() {
    val system = ActorSystem("clide",current.configuration.underlying.getConfig("clide"))
    this.system = Some(system)
    server = Some(system.actorOf(Props[UserServer], "users"))
  }
  
  def shutdown() {
    system.map(_.shutdown())
  }
}