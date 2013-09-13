package clide.actors

import akka.actor._
import clide.models._
import play.api.Play.current
import play.api.db.slick._
import scala.slick.driver.H2Driver.simple._

class SessionActor(
    var session: SessionInfo, 
    val user: UserInfo, 
    var project: ProjectInfo,
    var userActor: ActorRef,
    var projectActor: ActorRef,
    var peer: ActorRef) extends Actor with ActorLogging {
  import clide.actors.Messages._
  import clide.actors.Events._      
   
  def receive = {
    // echoing
    case any => sender ! any
  }
  
  override def preStart() {
    peer ! SessionStarted
  }
}