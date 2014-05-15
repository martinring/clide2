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

package clide.scala

import java.io.FileWriter
import scala.Array.canBuildFrom
import scala.collection.mutable.Map
import scala.sys.process.stringSeqToProcess
import clide.assistants._
import clide.collaboration._
import clide.models._
import scala.reflect.io.VirtualDirectory
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.collection.mutable.SortedSet

object Scala extends AssistantServer(ScalaBehavior)

case class ScalaBehavior(control: AssistantControl) extends AssistBehavior with ScalaCompiler {    
  val mimeTypes = Set("text/x-scala")

  val log = control.log
  
  val files = collection.mutable.Map.empty[String,OpenedFile]
  
  var project: ProjectInfo = null
    
  implicit val ec = scala.concurrent.ExecutionContext.Implicits.global

  def start(project: ProjectInfo) = {
    this.project = project
    noop
  }

  def stop = noop

  def annotate() {    
    messages.foreach { case (path,messages) =>
      println(path, messages)
      var annotations = new Annotations
      var last = 0
      messages.foreach {
	      case (offset, length, tpe, msg) =>
	        if (offset > last) {
	          annotations = annotations.plain(offset - last)
	          last = offset
	        }
	        annotations = annotations.annotate(length, 
	          tpe match {
	            case "error" =>   List(AnnotationType.Class -> "error", AnnotationType.ErrorMessage -> msg)
	            case "warning" => List(AnnotationType.InfoMessage -> msg)
	            case _ =>         List(AnnotationType.InfoMessage -> msg)
	          }
	        )
	        last += length
      }
      val file = files(path)
      annotations = annotations.plain(file.state.length)
      control.annotate(file, "messages", annotations)
    }    
  }
  
  def fileOpened(file: OpenedFile) = Future {
    reset()
    compile(file)
    files += file.info.path.mkString("/") -> file
    messages += file.info.path.mkString("/") -> SortedSet.empty
    annotate()
  }

  def fileActivated(file: OpenedFile) = Future {
    reset()
    compile(file)
    files += file.info.path.mkString("/") -> file
    annotate()
  }

  def fileInactivated(file: OpenedFile) = noop

  def fileClosed(file: OpenedFile) = noop

  def fileChanged(file: OpenedFile, delta: Operation, cursors: Seq[Cursor]) = Future {
    reset()
    files += file.info.path.mkString("/") -> file
    compile(file)    
    cursors.foreach(x => complete(x.anchor))
    annotate()
  }

  def collaboratorJoined(who: SessionInfo) = noop

  def collaboratorLeft(who: SessionInfo) = noop

  def cursorMoved(cursor: Cursor) = noop
   
  def annotationsRequested(file: OpenedFile, name: String) = noop
  
  def annotationsDisregarded(file: OpenedFile, name: String) = noop
  
  def receiveChatMessage(from: SessionInfo, msg: String, tpe: Option[String], timestamp: Long) = noop
  
  def helpRequest(from: SessionInfo, file: OpenedFile, pos: Int, id: String, request: String) = Future {
    control.annotate(file, "autocompletion", (new Annotations).respond(id, "Some Value"))
    println(id,file,pos,request,from)
  }
}

object ScalaApp extends App {
  Scala.startup()
  readLine()
  Scala.shutdown()
}
