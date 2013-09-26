package clide.plugins

import com.typesafe.config.Config
import clide.models.ProjectInfo
import akka.actor.Props

class IsabelleAssistant extends Assistant {
  import isabelle._
  
  override def preStart() {
    Isabelle_System.init()
    super.preStart()
  }
  
  def createSession(project: ProjectInfo) = {
    context.actorOf(Props(classOf[IsabelleAssistantSession],project),s"p${project.id}")    
  }
}