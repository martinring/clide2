package models.ot

import org.specs2.mutable._
import org.specs2.ScalaCheck
import play.api.libs.concurrent.Akka._
import play.api.Play.current
import play.api.test._
import play.api.test.Helpers._
import akka.actor.ActorDSL._
import akka.testkit._
import akka.actor.ActorSystem

class OTSpec extends TestKit(ActorSystem("OTSpec")) with ImplicitSender {  
  val server = system.actorOf(Server.props(new Document("Hallo")))
  
  def client(name: String) = actor(new Act{
    
  })
}