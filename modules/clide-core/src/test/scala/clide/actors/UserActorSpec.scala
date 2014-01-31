package clide.actors

import akka.testkit.TestKit
import akka.actor._
import scala.concurrent.duration._
import scala.language.postfixOps
import clide.models.LoginInfo
import java.util.UUID

class UserActorSpec extends TestKit(ActorSystem("test")) with ActorSpec {
  val setup = new TestSetup
  import setup._

  lazy val userActor1 = system.actorOf(UserActor.props(testUser1))
  lazy val userActor2 = system.actorOf(UserActor.props(testUser2))
  lazy val userActor3 = system.actorOf(UserActor.props(testUser3))
  
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
        case e: Events.UserProjectInfos if e.userProjects == projects(testUser2).toSet && e.collaborating.isEmpty => // 
      }
    }
    
    "must correctly initialize a backstage session" in {
      userActor3 ! Messages.internal.Anonymous(Messages.Login("password", true))
      val key = expectMsgPF(250 millis) {
        case Events.LoggedIn(`testUser3`, info) => info.key        
      }
      
      userActor3 ! Messages.internal.Identified(key, Messages.StartBackstageSession)
      val socket = expectMsgPF(250 millis) {
        case Events.EventSocket(ref, id) => ref
      }      
    }
    
    "must refuse a backstage session for anonymous users" in {
      userActor3 ! Messages.internal.Anonymous(Messages.StartBackstageSession)
      expectMsg(250 millis, Events.NotAllowed)    
    }
    
    "must refuse a backstage session for unauthorized external users" in {  
      userActor2 ! Messages.internal.External(testUser2, LoginInfo(testUser2.name, UUID.randomUUID().toString(), None, true), Messages.StartBackstageSession)
      expectMsg(250 second, Events.NotAllowed)      
    }
  }
  
  "A BackstageSession" must {
    userActor3 ! Messages.internal.Anonymous(Messages.Login("password", true))
    val key = expectMsgPF(250 millis) {
      case Events.LoggedIn(`testUser3`, info) => info.key        
    }
    
    userActor3 ! Messages.internal.Identified(key, Messages.StartBackstageSession)
    val socket = expectMsgPF(250 millis) {
      case Events.EventSocket(ref, id) => ref
    }
    
    "return a list of the projects" in {
      socket ! Messages.BrowseProjects
      val infos = expectMsgPF(250 millis) {
        case e: Events.UserProjectInfos if e.userProjects == projects(testUser3).toSet && e.collaborating.isEmpty => //
      }
    }
    
    "indicate when projects are created and deleted" in {
      socket ! Messages.CreateProject("test-project-222",None,false)
      val p = expectMsgPF(250 millis) {
        case e: Events.CreatedProject if e.project.name == "test-project-222" && e.project.owner == testUser3.name => e.project
      }      
      socket ! Messages.WithProject(p.name, Messages.DeleteProject)
      val ack = expectMsgPF(250 millis) {
        case e: Events.DeletedProject if e.project.name == p.name && e.project.id == p.id => true         
      }
    }
  }
}