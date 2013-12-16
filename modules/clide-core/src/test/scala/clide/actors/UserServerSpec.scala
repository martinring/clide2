package clide.actors

import akka.testkit.TestKit
import akka.actor.ActorSystem
import scala.concurrent.duration._
import clide.models.UserInfo
import com.typesafe.config.Config
import com.typesafe.config.ConfigFactory

class UserServerSpec extends TestKit(ActorSystem("test")) with ActorSpec {
  val setup = new TestSetup
  import setup._
  
  val userServer = system.actorOf(UserServer.props, "users")
  
  "the user server" must {
    "refuse a login for non existent user" in {
      userServer ! Messages.AnonymousFor("someUser", Messages.Login("password"))
      expectMsg(1.second, Events.DoesntExist)
    }
    
    "verify username, password and email address" in {
      info("empty username")
      userServer ! Messages.SignUp("","vaild@hotmail.com","vaildpwd")
      expectMsgPF(1.second){
        case Events.ActionFailed(errors) if errors.isDefinedAt("name") =>
      }       
      info("invalid email")
      userServer ! Messages.SignUp("vaild","invalid","vaildpwd")
      expectMsgPF(1.second){
        case Events.ActionFailed(errors) if errors.isDefinedAt("email") =>
      }       
      info("empty password")
      userServer ! Messages.SignUp("vaild","vaild@hotmail.com","")
      expectMsgPF(1.second){
        case Events.ActionFailed(errors) if errors.isDefinedAt("password") =>
      }       
    }
    
    "allow to signup a user and return the correct data" in {
      userServer ! Messages.SignUp("test","test@hotmail.com","password")
      expectMsg(1.second, Events.SignedUp(UserInfo("test","test@hotmail.com")))
    }
    
    "route the login message to the correct child" in {
      userServer ! Messages.AnonymousFor("test",Messages.Login("password", true))
      expectMsgPF(1.second) {
        case Events.LoggedIn(UserInfo("test","test@hotmail.com"), login) if login.isHuman && login.user == "test" =>
      }
    }
  }
}