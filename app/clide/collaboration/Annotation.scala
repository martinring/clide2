package clide.collaboration

import play.api.libs.json._
import scala.util._
import scala.annotation.tailrec
import clide.util.compare._

sealed trait Annotation
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

case class AnnotationStream(annotations: List[Annotation]) extends AnyVal {
  override def toString = Json.stringify(Json.toJson(this)(AnnotationStream.AnnotationStreamFormat))
}

object AnnotationStream {
  implicit object AnnotationStreamFormat extends Format[AnnotationStream] {
    def reads(json: JsValue) = 
      Json.fromJson[List[Annotation]](json).map(AnnotationStream.apply)
    def writes(value: AnnotationStream) = 
      Json.toJson(value.annotations)
  }
      
  private def extend(n: Int, as: List[Annotation]): List[Annotation] = as match {
    case Plain(m)::xs      => Plain(n+m)::xs
    case Annotate(m,c)::xs => Annotate(n+m,c)::xs
    case xs                => Plain(n)::xs
  }
  
  private def addPlain(n: Int, as: List[Annotation]): List[Annotation] = as match {
    case Plain(m)::xs => Plain(n+m)::xs
    case xs => Plain(n)::xs
  }
  
  private def addAnnotate(n: Int, c: Map[String,String], as: List[Annotation]): List[Annotation] = as match {
    case Annotate(m,c2)::xs if c2 == c => Annotate(n+m,c)::xs
    case xs => Annotate(n,c)::xs
  }
       
  def transform(as: AnnotationStream, os: Operation): Try[AnnotationStream] = {  
    @tailrec
    def loop(as: List[Annotation], os: List[Action], xs: List[Annotation]): Try[List[Annotation]] = (as,os,xs) match {
      case (Nil,Nil,xs) => Success(xs)
      case (aa@(a::as),bb@(b::bs),xs) => (a,b) match {
        case (_,Insert(i)) => loop(aa,bs,extend(i.length,xs))        
        case (Plain(n),Retain(m)) => (n <=> m) match {
          case LT => loop(as,Retain(m-n)::bs,addPlain(n,xs))
          case EQ => loop(as,bs,addPlain(n,xs))
          case GT => loop(Plain(n-m)::as,bs,addPlain(m,xs))
        }
        case (Annotate(n,c),Retain(m)) => (n <=> m) match {
          case LT => loop(as,Retain(m-n)::bs,addAnnotate(n,c,xs))
          case EQ => loop(as,bs,addAnnotate(n,c,xs))
          case GT => loop(Annotate(n-m,c)::as,bs,addAnnotate(m,c,xs))
        }
        case (Plain(r),Delete(d)) => (r <=> d) match {
          case LT => loop(as,Delete(d-r)::bs,xs)
          case EQ => loop(as,bs,xs)
          case GT => loop(Plain(r-d)::as,bs,xs)
        }
        case (Annotate(r,c),Delete(d)) => (r <=> d) match {
          case LT => loop(as,Delete(d-r)::bs,xs)
          case EQ => loop(as,bs,xs)
          case GT => loop(Annotate(r-d,c)::as,bs,xs)
        }        
      }
      case (Nil,Insert(i)::bs,xs) => loop(Nil,bs,addPlain(i.length,xs))      
      case _ => Failure(new Exception("the annotation stream could not be transformed"))
    }
    loop(as.annotations,os.actions,Nil).map { a => AnnotationStream(a.reverse) } 
  }
} 