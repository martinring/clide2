package clide.collaboration

import scala.util._
import scala.annotation.tailrec
import clide.util.compare._

/**
 * @author Martin Ring
 */
sealed trait Annotation { 
  val length: Int
  def withLength(n: Int): Annotation = this match {
    case Plain(_) => Plain(n)
    case Annotate(_,c) => Annotate(n,c)
  }
  
  override def toString = this match {
    case Plain(n)    => n.toString
    case Annotate(n,c) => "" // TODO
  }
}
case class Plain(length: Int) extends Annotation {
  override def toString = length.toString
}
case class Annotate(length: Int, content: Map[String,String]) extends Annotation {
  override def toString = length.toString + ":{" + content.map{case(k,v)=>k+": " +v}.mkString(",") + "}"
}

object AnnotationDiff {
  trait AnnotationDiff
  case class ChangeLength(n: Int) extends AnnotationDiff
  case class ChangeContent(c: Map[String,String]) extends AnnotationDiff
  case class Delete(n: Int) extends AnnotationDiff
  case class Insert(a: Annotations) extends AnnotationDiff
  
  def diff(a: Annotations, b: Annotations): Map[Int,AnnotationDiff] = {    
    null
  }
}

case class Annotations(annotations: List[Annotation] = Nil) extends AnyVal {
  override def toString = annotations.mkString(";")
  
  def annotate(n: Int, c: Map[String,String]): Annotations = {
    annotations.lastOption match {
      case Some(Annotate(m,c2)) if c == c2 => Annotations(annotations.init :+ Annotate(n+m,c))
      case _ => Annotations(annotations :+ Annotate(n,c))
    }
  }
  
  def plain(n: Int): Annotations = {
    annotations.lastOption match {
      case Some(Plain(m)) => Annotations(annotations.init :+ Plain(n+m))
      case _ => Annotations(annotations :+ Plain(n))
    }
  }
  
  def :+ (a: Annotation): Annotations = {
    (annotations.lastOption,a) match {
      case (Some(Plain(n)),Plain(m)) => Annotations(annotations.init :+ Plain(n+m))
      case (Some(Annotate(n,c)),Annotate(m,d)) if c == d => Annotations(annotations.init :+ Annotate(n+m,c))
      case _ => Annotations(annotations :+ a)
    }
  }
}

object Annotations {  
  private def addPlain(n: Int, as: List[Annotation]): List[Annotation] = as match {
    case Plain(m)::xs => Plain(n+m)::xs
    case xs if n > 0 => Plain(n)::xs
    case _ => as
  }
  
  private def addAnnotate(n: Int, c: Map[String,String], as: List[Annotation]): List[Annotation] = as match {
    case Annotate(m,c2)::xs if c2 == c => Annotate(n+m,c)::xs
    case xs => Annotate(n,c)::xs
  }
  
  private def add(a: Annotation, as: List[Annotation]): List[Annotation] = a match {
    case Plain(n) => addPlain(n,as)
    case Annotate(n,c) => addAnnotate(n,c,as)
  }
  
  private def addWithLength(n: Int, a: Annotation, as: List[Annotation]): List[Annotation] = a match {
    case Plain(_)      => addPlain(n,as)
    case Annotate(_,c) => addAnnotate(n,c,as)
  }
  
  def transform(a: Annotations, o: Operation): Try[Annotations] = {  
    @tailrec
    def loop(as: List[Annotation], bs: List[Action], xs: List[Annotation]): Try[List[Annotation]] = (as,bs,xs) match {
      case (Nil,Nil,xs) => Success(xs)
      case (aa@(a::as),bb@(b::bs),xs) => (a,b) match {        
        case (a,Insert(i)) => loop(aa,bs,addWithLength(i.length,a,xs))
        case (a,Retain(m)) => (a.length <=> m) match {
          case LT => loop(as,Retain(m-a.length)::bs,addWithLength(a.length,a,xs))
          case EQ => loop(as,bs,addWithLength(a.length,a,xs))
          case GT => loop(addWithLength(a.length-m,a,as),bs,addWithLength(m,a,xs))
        }
        case (a,Delete(d)) => (a.length <=> d) match {
          case LT => loop(as,Delete(d-a.length)::bs,xs)
          case EQ => loop(as,bs,xs)
          case GT => loop(addWithLength(a.length-d,a,as),bs,xs)
        }         
      }
      case (Nil,Insert(i)::bs,xs) => loop(Nil,bs,addPlain(i.length,xs))
      case _ => Failure(new Exception("the annotation couldn't be transformed because they haven't been applied to the same document"))
    }
    loop(a.annotations,o.actions,Nil).map(as => Annotations(as.reverse))
  }
}