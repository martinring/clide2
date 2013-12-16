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
import clide.actors.ActorSpec
import clide.collaboration.Operation
import clide.collaboration.Insert
import clide.actors.TestSetup

class FolderActorSpec extends TestKit(ActorSystem("test")) with ActorSpec {
  val setup = new TestSetup
  import setup._   
  
  val root = system.actorOf(FolderActor.props(testProject1a, None, "root"))
  val path = Seq("subfolder","bar.thy")
  var id: Long = -1
  
  "A folder actor hierarchy" must {
    "be empty to start with" in {
      root ! Messages.BrowseFolder
      expectMsgPF(1 second) {
        case Events.FolderContent(info,content) if content.isEmpty && info.project == testProject1a.id => info 
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
    
    "create the correct mime-types for files" in {
      root ! Messages.WithPath(path, Messages.TouchFile)
      expectMsgPF(1 second) {
        case Events.FileCreated(file) if file.mimeType == Some("text/x-isabelle") => file.id
      }
    }
    
    val testSessionHuman = SessionInfo(0, testUser1.name, "cyan", testProject1a.id, true, true)      
    
    "return an empty otstate for new files and return an acknowledgement when editing a file" in {
      root ! Messages.WithPath(path, Messages.internal.OpenFile(testSessionHuman))
      val id = expectMsgPF(1 second) {
        case Events.internal.OTState(info, content@"", revision@0) => info.id
      }
      root ! Messages.WithPath(path, Messages.Edit(id, 0, Operation(List(Insert("hallo")))))
      expectMsgPF(1 second) {
        case Events.AcknowledgeEdit(`id`) => true
      }
    }
  }    
}