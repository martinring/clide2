package clide.actors

import akka.actor._
import akka.testkit._
import org.scalatest.WordSpecLike
import org.scalatest.matchers.MustMatchers
import org.scalatest.BeforeAndAfterAll
import clide.persistence.Schema
import clide.persistence.DBAccess
import clide.models._
import scala.slick.session.Session
import clide.actors.files.FolderActor
import org.scalatest.Matchers

trait ActorSpec extends ImplicitSender with WordSpecLike with Matchers with BeforeAndAfterAll { self: TestKit =>   
  
  override def afterAll {
    TestKit.shutdownActorSystem(system)
  }
        
  lazy val schema = new Schema(scala.slick.driver.H2Driver)  
  
  lazy val db = slick.session.Database.forURL(
    url      = "jdbc:h2:test",
    user     = "sa",
    password = "",
    driver   = "org.h2.Driver")
    
  implicit val dbAccess = DBAccess(db,schema)
    
  val testUser    = UserInfo("test-user", "test@clide.flatmap.net") withPassword "banana"  
  
  import schema._
}