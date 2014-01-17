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
 * originally adapted from Tim Baumanns Haskell OT library (MIT-License)
 * @see https://github.com/Operational-Transformation/ot.hs
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
}

/** Skip the next `n` positions */
case class Retain(n: Int) extends Action { require(n>=0) }
/** Insert the given text at the current position */
case class Insert(s: String) extends Action
/** Delete the next `n` characters */
case class Delete(n: Int) extends Action { require(n>=0) }

case class Operation(actions: List[Action]) extends AnyVal {
  override def toString = "[" + actions.mkString(",") + "]"
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

  private def canonicalize(ops: List[Action]): List[Action] = {
    @tailrec
	def loop(as: List[Action], bs: List[Action]): List[Action] = (as,bs) match {
	  case (as,Nil) => as
	  case (as,Retain(n)::bs) =>
	    if (n == 0) loop(as,bs)
	    else loop(addRetain(n,as),bs)
	  case (as,Insert(i)::bs) =>
	    if (i == "") loop(as,bs)
	    else loop(addInsert(i,as),bs)
	  case (as,Delete(d)::bs) =>
	    if (d == 0) loop(as,bs)
	    else loop(addDelete(d,as),bs)
    }
	loop(Nil,ops.reverse).reverse
  }

  def transform(a: Operation, b: Operation): Try[(Operation, Operation)] = {
    @tailrec
    def loop(as: List[Action], bs: List[Action], xs: List[Action], ys: List[Action]): Try[(List[Action],List[Action])] = (as,bs,xs,ys) match {
      case (Nil,Nil,xs,ys) => Success((xs,ys))
      case (aa@(a::as),bb@(b::bs),xs,ys) => (a,b) match {
        case (Insert(i),_) => loop(as,bb,addInsert(i,xs),addRetain(i.length,ys))
        case (_,Insert(i)) => loop(aa,bs,addRetain(i.length,xs),addInsert(i,ys))
        case (Retain(n),Retain(m)) => (n <=> m) match {
          case LT => loop(as,Retain(m-n)::bs,addRetain(n,xs),addRetain(n,ys))
          case EQ => loop(as,bs,addRetain(n,xs),addRetain(n,ys))
          case GT => loop(Retain(n-m)::as,bs,addRetain(m,xs),addRetain(m,ys))
        }
        case (Delete(n),Delete(m)) => (n <=> m) match {
          case LT => loop(as,Delete(m-n)::bs,xs,ys)
          case EQ => loop(as,bs,xs,ys)
          case GT => loop(Delete(n-m)::as,bs,xs,ys)
        }
        case (Retain(r),Delete(d)) => (r <=> d) match {
          case LT => loop(as,Delete(d-r)::bs,xs,addDelete(r,ys))
          case EQ => loop(as,bs,xs,addDelete(d,ys))
          case GT => loop(Retain(r-d)::as,bs,xs,addDelete(d,ys))
        }
        case (Delete(d),Retain(r)) => (d <=> r) match {
          case LT => loop(as,Retain(r-d)::bs,addDelete(d,xs),ys)
          case EQ => loop(as,bs,addDelete(d,xs),ys)
          case GT => loop(Delete(d-r)::as,bs,addDelete(r,xs),ys)
        }
      }
      case (Nil,Insert(i)::bs,xs,ys) => loop(Nil,bs,addRetain(i.length,xs),addInsert(i,ys))
      case (Insert(i)::as,Nil,xs,ys) => loop(as,Nil,addInsert(i,xs),addRetain(i.length,ys))
      case _ => Failure(new Exception("the operations cannot be transformed: input-lengths must match"))
    }
    loop(a.actions,b.actions,Nil,Nil).map { case (a,b) => (Operation(a.reverse), Operation(b.reverse)) }
  }

  def compose(a: Operation, b: Operation): Try[Operation] = {
    @tailrec
    def loop(as: List[Action], bs: List[Action], xs: List[Action]): Try[List[Action]] = (as,bs,xs) match {
      case (Nil,Nil,xs) => Success(xs)
      case (aa@(a::as),bb@(b::bs),xs) => (a,b) match {
        case (Delete(d),_) => loop(as,bb,addDelete(d,xs))
        case (_,Insert(i)) => loop(aa,bs,addInsert(i,xs))
        case (Retain(n),Retain(m)) => (n <=> m) match {
          case LT => loop(as,Retain(m-n)::bs,addRetain(n,xs))
          case EQ => loop(as,bs,addRetain(n,xs))
          case GT => loop(Retain(n-m)::as,bs,addRetain(m,xs))
        }
        case (Retain(r),Delete(d)) => (r <=> d) match {
          case LT => loop(as,Delete(d-r)::bs,addDelete(r,xs))
          case EQ => loop(as,bs,addDelete(d,xs))
          case GT => loop(Retain(r-d)::as,bs,addDelete(d,xs))
        }
        case (Insert(i),Retain(m)) => (i.length <=> m) match {
          case LT => loop(as,Retain(m-i.length)::bs,addInsert(i,xs))
          case EQ => loop(as,bs,addInsert(i,xs))
          case GT => val (before,after) = i.splitAt(m)
                     loop(Insert(after)::as,bs,addInsert(before,xs))
        }
        case (Insert(i),Delete(d)) => (i.length <=> d) match {
          case LT => loop(as,Delete(d-i.length)::bs,xs)
          case EQ => loop(as,bs,xs)
          case GT => loop(Insert(i.drop(d))::as,bs,xs)
        }
      }
      case _ => Failure(new Exception("the operations cannot be composed: output-length of a must match input-length of a"))
    }
    loop(a.actions,b.actions,Nil).map(x => Operation(x.reverse))
  }
}
