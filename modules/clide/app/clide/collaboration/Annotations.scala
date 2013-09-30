package clide.collaboration

import play.api.libs.json._
import scala.util._
import scala.annotation.tailrec

sealed trait Annotation { 
  val length: Int
  def withLength(n: Int): Annotation = this match {
    case Plain(_) => Plain(n)
    case Annotate(_,c) => Annotate(n,c)
  }
}
case class Plain(length: Int) extends Annotation
case class Annotate(length: Int, content: Map[String,String]) extends Annotation

object Annotation {
  implicit object AnnotationFormat extends Format[Annotation] {
    def reads(json: JsValue): JsResult[Annotation] = json match {
      case JsNumber(n) if n > 0      => JsSuccess(Plain(n.toInt))
      case obj: JsObject             => for {
        length <- (obj \ "l").validate[Int]
        content <- (obj \ "c").validate[Map[String,String]]
      } yield Annotate(length,content)
      case _                         => JsError("cant parse action: expected number or object")
    }
    def writes(a: Annotation): JsValue = a match {
      case Plain(n) => JsNumber(n)
      case Annotate(n,c) => Json.obj("l" -> n, "c" -> c)      
    }
  }
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

case class Annotations(annotations: Vector[Annotation] = Vector.empty) extends AnyVal {
  override def toString = Json.stringify(Json.toJson(this)(Annotations.AnnotationsFormat))
  
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
  implicit object AnnotationsFormat extends Format[Annotations] {
    def reads(json: JsValue) = 
      Json.fromJson[Vector[Annotation]](json).map(Annotations.apply)
    def writes(value: Annotations) = 
      Json.toJson(value.annotations)
  }     
  
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
  
  def transform(a: Annotations, o: Operation): Try[Annotations] = Try {  
    @tailrec
    def loop(as: List[Annotation], os: List[Action], result: Annotations): Annotations = as match {
      case a::ass => os match {
        case Insert(s)::oss =>
          loop(as,os,result :+ a.withLength(s.length))
        case Retain(n)::oss if a.length < n =>  
          loop(ass,Retain(n-a.length)::oss,result :+ a)
        case Retain(n)::oss =>
          loop(addWithLength(a.length - n, a, ass),oss,result :+ a.withLength(n))
        case Delete(n)::oss if a.length < n =>  
          loop(ass,Retain(n-a.length)::oss,result)
        case Delete(n)::oss =>
          loop(addWithLength(a.length - n, a, ass),oss,result)
      }        
      case Nil => os match {
        case Nil => result
        case _ => sys.error("lengths don't match")
      }
    }
    loop(a.annotations.toList,o.actions,Annotations())
  }
}