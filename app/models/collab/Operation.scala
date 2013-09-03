/**
 * adapted from Tim Baumanns Haskell OT library
 * @see https://github.com/Operational-Transformation/ot.hs
 * @author Martin Ring
 */
package models.collab

import play.api.libs.json._
import play.api.libs.functional.syntax._
import scala.util.Try
import scala.util.Success
import scala.util.Failure
import scala.annotation.tailrec
import _root_.util.compare._

sealed trait Action {
  override def toString = Action.ActionFormat.writes(Action.this).toString
}
/** Skip the next `n` positions */
case class Retain(n: Int) extends Action { assume(n>=0) }
/** Insert the given text at the current position */
case class Insert(s: String) extends Action
/** Delete the next `n` characters */
case class Delete(n: Int) extends Action { assume(n>=0) }

object Action {    
  implicit object ActionFormat extends Format[Action] {
    def reads(json: JsValue): JsResult[Action] = json match {
      case JsNumber(n) if n > 0      => JsSuccess(Retain(n.toInt))
      case JsNumber(n) if n < 0      => JsSuccess(Delete(-n.toInt))
      case JsString(s) if s.nonEmpty => JsSuccess(Insert(s))
      
      case _                         => JsError("cant parse action: expected number, string or object")
    }
    def writes(action: Action): JsValue = action match {
      case Retain(n) => JsNumber(n)
      case Delete(n) => JsNumber(-n)
      case Insert(s) => JsString(s)
    }
  }
}

case class Operation(actions: List[Action]) extends AnyVal {
  override def toString = Json.stringify(Json.toJson(Operation.this)(Operation.SourceOperationFormat))
}

object Operation {
  implicit object SourceOperationFormat extends Format[Operation] {
    def reads(json: JsValue) = 
      Json.fromJson[List[Action]](json).map(Operation.apply)
    def writes(value: Operation) = 
      Json.toJson(value.actions)
  }
  
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
      case _ => Failure(new Exception("the operations couldn't be transformed because they haven't been applied to the same document"))
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
      case (Delete(d)::as,Nil,xs) => loop(as,Nil,addDelete(d,xs))
      case (Nil,Insert(i)::bs,xs) => loop(Nil,bs,addInsert(i,xs))
      case _ => Failure(new Exception("the operations couldn't be composed since their lengths don't match"))
    }
    loop(a.actions,b.actions,Nil).map(x => Operation(x.reverse))
  } 
}