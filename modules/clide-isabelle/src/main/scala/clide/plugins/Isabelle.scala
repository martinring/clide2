package clide.plugins

import akka.actor._
import com.typesafe.config.ConfigFactory
import scala.concurrent.duration._
import clide.actors.Messages._
import clide.actors.Events._
import clide.models._
import isabelle.Thy_Load
import clide.collaboration.Document
import isabelle.Session
import isabelle.Outer_Syntax
import clide.collaboration.Annotate
import clide.collaboration.Plain
import clide.collaboration.Annotations
import clide.collaboration.Annotation

object Isabelle extends App {
  val system = ActorSystem("clide-isabelle",ConfigFactory.load.getConfig("clide-isabelle"))    
  val plugin = system.actorOf(Props[IsabelleAssistant],"plugin")
  readLine()  
  plugin ! PoisonPill
}