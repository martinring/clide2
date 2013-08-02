package models.ot

import scala.util.{Try,Success,Failure}
import scala.reflect.ClassTag
import akka.actor.{Actor,Props}

case class Document(stream: List[Char]) extends AnyVal {
  def apply(op: Operation): Try[Document] = {
    def loop(ops: List[Action], it: List[Char], ot: List[Char]): Try[List[Char]] = (ops,it,ot) match {
      case (Nil,Nil,ot) => Success(ot)
      case (op::ops,it,ot) => op match {
        case Retain(r) => if (it.length < r)
            Failure(new Exception("operation can't be applied to the document: operation is longer than the text"))
          else {
            val (before,after) = it.splitAt(r)
            loop(ops,after,ot ++ before)
          }
        case Insert(i) => loop(ops,it,ot ++ i.toList)
        case Delete(d) => if (d > it.length)
            Failure(new Exception( "operation can't be applied to the document: operation is longer than the text"))
          else loop(ops,it.drop(d),ot)             
      }
      case _ => Failure(new Exception("operation can't be applied to the document: text is longer than the operation"))
    }
    loop(op.actions,stream,Nil).map(Document)
  }    
}