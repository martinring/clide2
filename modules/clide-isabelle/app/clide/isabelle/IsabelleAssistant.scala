package clide.isabelle

import akka.actor.Props
import clide.assistants.Assistant
import clide.models.ProjectInfo

class IsabelleAssistant extends Assistant {
  def createSession(project: ProjectInfo) = {
    context.actorOf(Props(classOf[IsabelleAssistantSession],project),s"p${project.id}")    
  }
}