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

class TestSetup {
  val schema = new Schema(scala.slick.driver.H2Driver)  
  
  val db = slick.session.Database.forURL(
    url      = "jdbc:h2:mem:test;DB_CLOSE_DELAY=-1",
    user     = "sa",
    password = "",
    driver   = "org.h2.Driver")
    
  implicit val dbAccess = DBAccess(db,schema)        
      
  val testUserPwd = "password"
    
  val testUser1   = UserInfo("test-user-1", "test1@clide.flatmap.net") withPassword testUserPwd
  val testUser2   = UserInfo("test-user-2", "test2@clide.flatmap.net") withPassword testUserPwd
  val testUser3   = UserInfo("test-user-3", "test3@clide.flatmap.net") withPassword testUserPwd
  
  import schema._
  
  db.withSession { implicit session: Session => 
    dropAllIfExist()
    createAllIfNotExist()
    UserInfos.insert(testUser1)
    UserInfos.insert(testUser2)
    UserInfos.insert(testUser3)
  }
  
  val (testProject1a, testProject2a,
       testProject2b, testProject3a,
       testProject3b, testProject3c) = db.withSession { implicit session: Session =>
    (ProjectInfos.create("test-project-1a", testUser1.name, None),
     ProjectInfos.create("test-project-2a", testUser2.name, None),
     ProjectInfos.create("test-project-2b", testUser2.name, None),
     ProjectInfos.create("test-project-3a", testUser3.name, None),
     ProjectInfos.create("test-project-3b", testUser3.name, None),
     ProjectInfos.create("test-project-3c", testUser3.name, None))
  }
  
  /*val (testFolder: FileInfo, testSubfolder: FileInfo,
       testFile) = db.withSession { implicit session: Session =>
    (FileInfos.create(testProject1a.id, Seq(), None, false, false, true, None),
     FileInfos.create(testProject1a.id, Seq("subfolder"), None, false, false, true, Some(testFolder.id)),
     FileInfos.create(testProject1a.id, Seq("file"), None, false, false, false, Some(testSubfolder.id)))
  } */ 
  
  val projects = Map(
    testUser1 -> List(testProject1a),
    testUser2 -> List(testProject2a, testProject2b),
    testUser3 -> List(testProject3a, testProject3b, testProject3c))  
}

trait ActorSpec extends ImplicitSender with WordSpecLike with Matchers with BeforeAndAfterAll { self: TestKit =>     
  override def afterAll {
    TestKit.shutdownActorSystem(system)
  }
}