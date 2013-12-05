package clide.actors.files

import akka.testkit._
import akka.actor._
import org.scalatest.WordSpecLike
import org.scalatest.matchers.MustMatchers
import org.scalatest.BeforeAndAfterAll
import clide.persistence.DBAccess
import clide.persistence.Schema
import scala.slick.session.Session
import clide.models._
import clide.actors.Messages
import clide.actors.Events
import scala.concurrent.duration._
import scala.language.postfixOps

class FileActorSpec(system: ActorSystem) extends TestKit(system) with ImplicitSender
  with WordSpecLike with MustMatchers with BeforeAndAfterAll {
  
  def this() = this(ActorSystem("file-test"))
  
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
  
  // Setup
  val testProject = db.withSession { implicit session: Session =>
    schema.reset
    UserInfos.insert(testUser)
    ProjectInfos.create("test-project","test-user",None)
  }   
  
  val root = system.actorOf(FolderActor.props(testProject, None, "root"))
  
  "A folder actor hierarchy" must {
    "be empty to start with" in {
      root ! Messages.BrowseFolder
      expectMsgPF(1 second) {
        case Events.FolderContent(info,content) if content.isEmpty && info.project == testProject.id => info 
      }
    }    
    
    "handle file creation and event registration" in {
      root ! Messages.Register
      root ! Messages.WithPath(Seq("subfolder","file.txt"), Messages.TouchFile)      
      expectMsgPF(1 second) {
        case Events.FileCreated(folder) if folder.path == Seq("subfolder") && folder.isDirectory => folder
      }
      expectMsgPF(1 second) {
        case Events.FileCreated(file) if file.path == Seq("subfolder","file.txt") && !file.isDirectory => file
      }
    }
    
    "handle event unregistering" in {
      root ! Messages.Unregister
      root ! Messages.WithPath(Seq("other","foo.thy"), Messages.TouchFile)
      expectNoMsg(1 second)
    }
    
    "not create a folder when exploring" in {
      root ! Messages.Register
      root ! Messages.WithPath(Seq("subfolder","bar","zap"), Messages.ExplorePath)
      expectMsgPF(1 second) {
        case Events.FolderContent(folder,content) if folder.path == Seq("subfolder") => folder
      }
      expectNoMsg(1 second)
    }
  }
}