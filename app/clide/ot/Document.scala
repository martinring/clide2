package clide.ot

import scala.util.{Try,Success,Failure}
import scala.reflect.ClassTag
import akka.actor.{Actor,Props}
import scala.annotation.tailrec

case class Document(content: String) {  
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