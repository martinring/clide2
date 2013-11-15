 /*            _ _     _                                                      *\
 **           | (_)   | |                                                     **
 **        ___| |_  __| | ___      clide 2                                    **
 **       / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
 **      | (__| | | (_| |  __/     http://clide.flatmap.net                   **
 **       \___|_|_|\__,_|\___|                                                **
 **                                                                           **
 **  This file is part of Clide.                                              **
 **                                                                           **
 **  Clide is free software: you can redistribute it and/or modify            **
 **  it under the terms of the GNU General Public License as published by     **
 **  the Free Software Foundation, either version 3 of the License, or        **
 **  (at your option) any later version.                                      **
 **                                                                           **
 **  Clide is distributed in the hope that it will be useful,                 **
 **  but WITHOUT ANY WARRANTY; without even the implied warranty of           **
 **  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
 **  GNU General Public License for more details.                             **
 **                                                                           **
 **  You should have received a copy of the GNU General Public License        **
 **  along with Clide.  If not, see <http://www.gnu.org/licenses/>.           **
 \*                                                                           */

package clide.collaboration

import scala.util.{Try,Success,Failure}
import scala.reflect.ClassTag
import akka.actor.{Actor,Props}
import scala.annotation.tailrec

/**
 * @author Martin Ring <martin.ring@dfki.de>
 */
case class Document(content: String) extends AnyVal {
  def apply(op: Operation): Try[Document] = {
    @tailrec
    def loop(ops: List[Action], it: String, ot: String): Try[String] = (ops,it,ot) match {
      case (Nil,"",ot) => Success(ot)
      case (op::ops,it,ot) => op match {
        case Retain(r) => if (it.length < r)
            Failure(new Exception("operation can't be applied to the document: operation is longer than the text"))
          else {
            val (before,after) = it.splitAt(r)
            loop(ops,after,ot ++ before)
          }
        case Insert(i) => loop(ops,it,ot + i)
        case Delete(d) => if (d > it.length)
            Failure(new Exception("operation can't be applied to the document: operation is longer than the text"))
          else loop(ops,it.drop(d),ot)
      }
      case _ => Failure(new Exception("operation can't be applied to the document: text is longer than the operation"))
    }
    loop(op.actions,content,"").map(new Document(_))
  }
}
