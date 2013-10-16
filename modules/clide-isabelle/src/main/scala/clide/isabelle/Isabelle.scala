package clide.isabelle

import com.typesafe.config.ConfigFactory

import akka.actor.ActorSystem
import akka.actor.Props
import akka.kernel.Bootable
import isabelle.Isabelle_System
import scala.concurrent.duration._

object Isabelle extends Bootable {
  val system = ActorSystem("clide-isabelle",ConfigFactory.load.getConfig("clide-isabelle"))
  
  def startup() {
    Isabelle_System.init()
    val plugin = system.actorOf(Props[IsabelleAssistant],"plugin")
  }
  
  def shutdown() {
    system.shutdown()
  }   
}

object IsabelleApp extends App {
  Isabelle.startup()
  readLine()
  Isabelle.shutdown()
  Isabelle.system.awaitTermination(5 seconds)
  sys.exit()
}