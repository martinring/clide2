package clide.plugins

import clide.models._
import clide.collaboration._

class IsabelleAssistantSession(project: ProjectInfo) extends AssistantSession(project: ProjectInfo) {
  import isabelle._
  
  var session: Session = null
  
  override def preStart() {
    session = new isabelle.Session(new isabelle.Thy_Load(Set.empty, isabelle.Outer_Syntax.empty))
    super.preStart()
  }  
  
  def processFile(file: OpenedFile) = Some {
    Annotations(session.thy_load.base_syntax.scan(file.state).map { case t: isabelle.Token =>
        (if (t.is_command) {
          Annotate(t.content.length(),Map("c"->"cm-keyword"))	       
	    } else if (t.is_comment) {
	      Annotate(t.content.length(),Map("c"->"cm-comment"))
	    } else if (t.is_string) {
	      Annotate(t.content.length(),Map("c"->"cm-string"))          
        } else Plain(t.content.length()))
      })
  }
}