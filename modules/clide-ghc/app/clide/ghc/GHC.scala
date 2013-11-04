package clide.ghc

import com.typesafe.config.ConfigFactory

import akka.actor.ActorSystem
import akka.actor.Props
import akka.kernel.Bootable
import scala.concurrent.duration._

object GHC extends Bootable {
  val system = ActorSystem("clide-ghc",ConfigFactory.load.getConfig("clide-ghc"))
  
  def startup() {
    val plugin = system.actorOf(Props[GHCAssistant],"plugin")
  }
  
  def shutdown() {
    system.shutdown()
  }   
}

object GHCApp extends App {
  GHC.startup()
  readLine()
  GHC.shutdown()
  GHC.system.awaitTermination(5 seconds)
  sys.exit()
}