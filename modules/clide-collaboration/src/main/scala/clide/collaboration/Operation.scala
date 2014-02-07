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

/**
 * @author Martin Ring
 */
package clide.collaboration

import scala.util.Try
import scala.util.Success
import scala.util.Failure
import scala.annotation.tailrec
import clide.util.compare._

sealed trait Action {
  override def toString = this match {
    case Retain(n) => n.toString
    case Insert(s) => "\""+s+"\""
    case Delete(n) => (-n).toString
  }
  
  def length = this match {
    case Retain(n) => n
    case Insert(s) => s.length
    case Delete(n) => n
  }
}

/** Skip the next `n` positions */
case class Retain(n: Int) extends Action { require(n>=0) }
/** Insert the given text at the current position */
case class Insert(s: String) extends Action
/** Delete the next `n` characters */
case class Delete(n: Int) extends Action { require(n>=0) }

trait SimpleAction

case class Operation(actions: List[Action]) {
  override def toString = "[" + actions.mkString(",") + "]"
      
  private def asSimpleOp: List[SimpleOperation.action[Char]] = actions.flatMap {
    case Retain(n) => List.fill(n)(SimpleOperation.Retain[Char])
    case Insert(s) => s.map(SimpleOperation.Insert(_))
    case Delete(n) => List.fill(n)(SimpleOperation.Delete[Char])
  }
}

object Operation {  
  private def addRetain(n: Int, ops: List[Action]): List[Action] = ops match {
    case Retain(m)::xs => Retain(n+m)::xs
    case xs            => Retain(n)::xs
  }

  private def addInsert(s: String, ops: List[Action]): List[Action] = ops match {
    case Delete(d)::xs => Delete(d)::addInsert(s,xs)
    case Insert(t)::xs => Insert(t+s)::xs
    case xs            => Insert(s)::xs
  }

  private def addDelete(n: Int, ops: List[Action]): List[Action] = ops match {
    case Delete(m)::xs => Delete(n+m)::xs
    case xs            => Delete(n)::xs
  }
  
  private def fromSimpleOp(op: List[SimpleOperation.action[Char]]): Operation = 
    Operation(op.foldLeft(List.empty[Action]) {
      case (r,SimpleOperation.Retain()) => addRetain(1,r)
      case (r,SimpleOperation.Insert(c)) => addInsert(c.toString,r)
      case (r,SimpleOperation.Delete()) => addDelete(1,r)
    })
  
  def transform(a: Operation, b: Operation): Try[(Operation, Operation)] =
    Try { SimpleOperation.transform(a.asSimpleOp,b.asSimpleOp).map{ case (a,b) => (fromSimpleOp(a), fromSimpleOp(b)) }.get }
    
  def compose(a: Operation, b: Operation): Try[Operation] = 
    Try { SimpleOperation.compose(a.asSimpleOp,b.asSimpleOp).map(fromSimpleOp).get } 
}
