/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */

package clide.isabelle

import isabelle._
import clide.assistants.AssistBehavior
import clide.models._
import scala.concurrent.Promise
import isabelle.Session
import isabelle.Build
import isabelle.Path
import isabelle.Document
import isabelle.XML
import isabelle.Isabelle_System
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.concurrent.Promise
import scala.language.postfixOps
import clide.assistants.Cursor
import scala.concurrent.Future

trait IsabelleSession { self: AssistBehavior with Control with IsabelleConversions =>
  var session: Session     = null
  var project: ProjectInfo = null
  var cursors = Set.empty[Cursor]

  var outdated = Set.empty[Document.Node.Name]

  private var files = scala.collection.mutable.Map.empty[Document.Node.Name,(scala.concurrent.Future[Document.Version],OpenedFile)]

  def updateFile(name: Document.Node.Name, file: OpenedFile, update: List[(Document.Node.Name,Document.Node.Edit[Text.Edit,Text.Perspective])]): scala.concurrent.Future[Unit] = {
    session.update(Document.Blobs.empty, update)
    val p = Promise[Document.Version]()
    val s = scala.concurrent.Future{
      control.annotate(file, "substitutions", IsabelleMarkup.substitutions(file.state))
      control.annotate(file, "sub/superscript", IsabelleMarkup.scripts(file.state))
    }(control.executionContext)

    val version = session.current_state.history.tip.version
    version.map(p.success)
    files(name) = (p.future, file)
    p.future.map(_ => ())(control.executionContext)
  }

  def refreshAnnotations() = {
    for {
      node    <- outdated
      snapshot = session.snapshot(node,Nil)
      version  = snapshot.version
    } for {
      (v,state) <- files.get(snapshot.node_name)
      if v.value.flatMap(_.toOption) == Some(snapshot.version)
    } {
      control.log.info("annotating snapshot {}", snapshot.node_name)
      control.annotate(state, "inner syntax", IsabelleMarkup.highlighting(snapshot))
      control.annotate(state, "output", IsabelleMarkup.output(snapshot, Set.empty))
      control.annotate(state, "errors", IsabelleMarkup.errors(snapshot))
      control.annotate(state, "warnings", IsabelleMarkup.warnings(snapshot))
      //control.annotate(state, "typing tooltips", IsabelleMarkup.typeInfo(snapshot))
      control.annotate(state, "progress", IsabelleMarkup.progress(state.state, snapshot))
    }
    outdated = Set.empty
  }

  def start(project: ProjectInfo) = {
    this.project = project
    val ops = isabelle.Options.init
    val initialized = Promise[Unit]()
    control.log.info("building session content")
    val content = Build.session_content(ops, false, Nil, "HOL")
    session = new Session(new Resources(content.loaded_theories, content.known_theories, content.syntax) {
      override def append(dir: String, source_path: Path): String = {
        control.log.info("thy_load.append({}, {})", dir, source_path)
        val path = source_path.expand
        if (dir == "" || path.is_absolute)           
          Isabelle_System.platform_path(path)
        else {
          (Path.explode(dir) + source_path).expand.implode
        }
      }      
    })    
    session.phase_changed += Session.Consumer("clide"){ p => p match {
      case Session.Startup  =>
        control.chat("I'm starting up, please wait a second!")
      case Session.Shutdown =>
        control.chat("I'm shutting down")
      case Session.Inactive =>
        control.stop()
      case Session.Failed   =>
        control.chat("I couldn't start")
        if (!initialized.isCompleted)
          initialized.failure(sys.error("isabelle session failed to initialize"))
      case Session.Ready    =>
        session.update_options(ops)
        if (!initialized.isCompleted)
          initialized.success(())
    } }
    session.syslog_messages += Session.Consumer("clide"){ msg =>
      control.log.info("SYSLOG: {}", XML.content(msg.body))
      control.chat(XML.content(msg.body))
    }
    session.commands_changed += Session.Consumer("clide"){ msg =>
      outdated ++= msg.nodes
    }
    session.start("clide", List("-S","HOL"))
    initialized.future
  }

  def stop = {    
    session.stop()
    noop
  }
}
