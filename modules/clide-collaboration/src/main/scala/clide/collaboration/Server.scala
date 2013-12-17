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

package clide.collaboration

import scala.reflect.ClassTag
import scala.util.{Try,Success,Failure}
import scala.collection.mutable.Buffer

class Server(initialState: Document) {
  private val history: Buffer[Operation] = Buffer.empty
  private var state: Document = initialState

  def text = state.content
  def revision = history.length
  def getHistory = history.view

  /**
   * an operation arrives from a client
   * @param rev the revision the client refers to
   */
  def applyOperation(operation: Operation, rev: Long): Try[Operation] = {
    val result = for {
	  concurrentOps <- Try {
	    require((0 to revision) contains rev, "invalid revision: " + rev)
	    history.view(rev.toInt, revision) // TODO: Long Revisions
	  }
	  operation <- concurrentOps.foldLeft(Success(operation): Try[Operation]) {
	    case (a,b) => a.flatMap(a => Operation.transform(a,b).map(_._1)) }
	  nextState <- state(operation)
	} yield (nextState, operation)
	result.map {
	  case (nextState,operation) =>
	    history.append(operation)
	    state = nextState
	    operation
	}
  }
  
  /**
   * transform a client annotation to fit the most recent revision
   * @param rev the revision the client refers to
   */
  def transformAnnotation(rev: Int, as: Annotations): Try[Annotations] = for {
      concurrentOps <- Try {
        require((0 to revision) contains rev, "invalid revision: " + rev)
        history.view(rev, revision)
      }
      annotation <- concurrentOps.foldLeft(Success(as): Try[Annotations]) {
        case (a,b) => a.flatMap(a => Annotations.transform(a,b)) }
  } yield annotation
}
