/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
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

package clide.haskell

import java.io.FileWriter

import scala.Array.canBuildFrom
import scala.collection.mutable.Map
import scala.sys.process.stringSeqToProcess

import clide.assistants._
import clide.collaboration._
import clide.models._

object Haskell extends AssistantServer(HaskellBehavior)

case class HaskellBehavior(control: AssistantControl) extends AssistantBehavior {
  val mimeTypes = Set("text/x-haskell")

  val log = control.log
  var project: ProjectInfo = null
  val cursorInfos: Map[Long,Map[Long,Annotations]] = Map.empty

  def start(project: ProjectInfo) {
    new java.io.File(project.root).mkdirs()
    this.project = project
    control.chat("i'm ready to go!")
  }

  def stop {
    log.info("ghc stopped")
  }

  def fileOpened(file: OpenedFile) {

  }

  def fileActivated(file: OpenedFile) {
    fileChanged(file,new Operation(List(Insert(file.state))),Seq.empty)
  }

  def fileInactivated(file: OpenedFile) {

  }

  def fileClosed(file: OpenedFile) {
    control.chat("closed " + file.toString)
    fileChanged(file,new Operation(List(Delete(file.state.length))),Seq.empty)
  }

  val Output = """^.*:([0-9]+):([0-9]+):(.*)$""".r

  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]) {
    control.annotate(file, "substitutions", HaskellMarkup.substitutions(file.state))

    val temp = new java.io.File(project.root + "/" + file.info.path.mkString("/"))
	val name = temp.getPath()

	val write = new FileWriter(temp)
	write.write(file.state)
	write.close()

	val lines = {
      val outer = Seq("ghc-mod","check",name).lines
      if (outer.nonEmpty) outer else
        Seq("ghc-mod","lint", name).lines
    }

	val errs = lines.collect {
      case Output(line,ch,msg)   => ((line.toInt,ch.toInt),if (msg.toLowerCase.contains("error")) "Error" else if (msg.toLowerCase.contains("warning")) "Warning" else "Info" ,msg)
    }

    log.info("lines: {}", errs)

    val as = HaskellMarkup.toAnnotations(errs.toList, file.state)

    control.annotate(file, "linting", as)

    cursors.foreach(cursorMoved)
  }

  def collaboratorJoined(who: SessionInfo){

  }

  def collaboratorLeft(who: SessionInfo){
    cursorInfos.values.foreach(_.remove(who.id))
  }

  def cursorMoved(cursor: Cursor){
    val temp = new java.io.File(project.root + "/" + cursor.file.info.path.mkString("/"))
    val name = temp.getPath()

    val before = cursor.file.state.take(cursor.anchor)
    val line = before.count(_ == '\n') + 1
    val col  = before.length - before.lastIndexOf('\n')

    val proc: Seq[String] = Seq("ghc-mod", "type", name, cursor.file.info.path.last.dropRight(3).capitalize, line.toString, col.toString)
    val lines = proc.lines

    val Line = "([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+) \"(.*)\"".r

    val as = lines.headOption.getOrElse("") match {
      case Line(fl,fc,tl,tc,msg) =>
        val lengths = cursor.file.state.split("\n").map(_.length + 1)
	    val from = lengths.take(fl.toInt - 1).sum + fc.toInt - 1
	    val to   = lengths.take(tl.toInt - 1).sum + tc.toInt - 1
	    new Annotations().plain(from).annotate(to-from,
	      Set(AnnotationType.InfoMessage -> HaskellMarkup.prettify(msg),AnnotationType.Class -> "info")).plain(cursor.file.state.length - to)
      case _ =>
 	    new Annotations().plain(cursor.file.state.length)
    }

    val cursors = cursorInfos.get(cursor.file.info.id).getOrElse {
      cursorInfos(cursor.file.info.id) = Map.empty
      cursorInfos(cursor.file.info.id)
    }

    if (!cursors.isDefinedAt(cursor.owner.id) || cursors(cursor.owner.id) != as) {
      cursors(cursor.owner.id) = as

      control.annotate(cursor.file, "cursor-info", cursors.values.reduce[Annotations]{
        case (a,b) => a.compose(b).get
      })
    }
  }
}

object HaskellApp extends App {
  Haskell.startup()
  readLine()
  Haskell.shutdown()
}
