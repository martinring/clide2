package clide.actors

import akka.testkit.TestKit
import akka.actor._
import scala.concurrent.duration._
import scala.language.postfixOps

class UserActorSpec extends TestKit(ActorSystem("test")) with ActorSpec {
  val userActor1 = system.actorOf(UserActor.props(testUser1))
  val userActor2 = system.actorOf(UserActor.props(testUser2))
  val userActor3 = system.actorOf(UserActor.props(testUser3))
  
  "A UserActor" must {
    "handle logins correctly" in {
      userActor1 ! Messages.internal.Anonymous(Messages.Login("password", true))
      val key1 = expectMsgPF(250 millis) {
        case Events.LoggedIn(`testUser1`, info) if info.isHuman == true && info.user == testUser1.name => info.key
      }
      userActor1 ! Messages.internal.Anonymous(Messages.Login("password", false))
      val key2 = expectMsgPF(250 millis) {
        case Events.LoggedIn(`testUser1`, info) if info.isHuman == false && info.user == testUser1.name => info.key
      }
      assert(key1 != key, "the login keys of two independent logins must not be equal")
      userActor1 ! Messages.internal.Anonymous(Messages.Login("wrong", false))
      expectMsg(100 millis, Events.WrongPassword)
    }
    
    "must return a list of the projects" in {
      userActor2 ! Messages.internal.Anonymous(Messages.Login("password", true))
      val key = expectMsgPF(250 millis) {
        case Events.LoggedIn(`testUser2`, info) => info.key        
      }
      
      userActor2 ! Messages.internal.Identified(key, Messages.BrowseProjects)
      expectMsgPF(250 millis) {
        case e: Events.UserProjectInfos if e.userProjects == projects(testUser2) && e.collaborating.isEmpty => // 
      }
    }
  }
}