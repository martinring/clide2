package clide.ghc

import akka.actor.Props
import clide.assistants.Assistant
import clide.models.ProjectInfo

class GHCAssistant extends Assistant {
  def createSession(project: ProjectInfo) = {
    context.actorOf(Props(classOf[GHCAssistantSession],project),s"p${project.id}")    
  }
}