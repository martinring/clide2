package clide

import akka.actor._
import com.typesafe.config.ConfigFactory

object Core extends App {
  val system = ActorSystem("clide",ConfigFactory.load.getConfig("clide"))
  
  system.actorOf(Props[HelloActor],"hello")
  
  class HelloActor extends Actor {
    def receive = {
      case "die" => system.shutdown()
      case msg => println(msg)
    }
  }
}