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
}
case class Plain(length: Int) extends Annotation {
  override def toString = length.toString
}

object AnnotationType extends Enumeration {
  val Class          = Value("c")
  val Tooltip        = Value("t")
  val ErrorMessage   = Value("e")
  val WarningMessage = Value("w")
  val InfoMessage    = Value("i")
  val Substitution   = Value("s")
  val Output         = Value("o")
}

case class Annotate(length: Int, content: Set[(AnnotationType.Value,String)]) extends Annotation {
  override def toString = length.toString + ":{" + content.map{case(k,v)=>k+": " +v}.mkString(",") + "}"
}

object AnnotationDiff {
  trait AnnotationDiffItem
  case class Leave(n: Int) extends AnnotationDiffItem
  case class Replace(n: Int, a: Annotations) extends AnnotationDiffItem       
    
  case class AnnotationDiff(items: List[AnnotationDiffItem] = Nil) extends AnyVal {
    def leave(n: Int = 1) = items.lastOption match {
      case Some(Leave(m)) => AnnotationDiff(items.init :+ Leave(n+m))
      case _              => AnnotationDiff(items :+ Leave(n))
    }        
    
    def insert(a: Annotation) = items.lastOption match {
      case Some(Replace(n,b)) => AnnotationDiff(items.init :+ Replace(n,b :+ a))
      case _                  => AnnotationDiff(items :+ Replace(0,Annotations(List(a))))
    }
    
    def insert(a: Annotations) = items.lastOption match {
      case Some(Replace(n,b)) => AnnotationDiff(items.init :+ Replace(n,Annotations(a.annotations ++ b.annotations)))
      case _                  => AnnotationDiff(items :+ Replace(0,a))
    }
    
    def delete(n: Int = 1) = items.lastOption match {
      case Some(Replace(m,a)) => AnnotationDiff(items.init :+ Replace(n+m,a))
      case _                  => AnnotationDiff(items :+ Replace(n,new Annotations()))
    }
    
    def weight = items.map({case Replace(_,a) => a.length; case _ => 0}).sum
    
    def isEmpty = items.length == 0 || items.length == 1 && items.head.isInstanceOf[Leave]
  }
    
  def diff(a: List[Annotation], b: List[Annotation], c: AnnotationDiff = new AnnotationDiff()): AnnotationDiff = (a,b) match {
    case (Nil,Nil)        => c
    case (aa@(a::as),Nil) => c.delete(aa.length)
    case (Nil,bb@(b::bs)) => c.insert(Annotations(bb))
    case (a::as,b::bs) if a == b => diff(as,bs,c.leave(1))
    case (a::as,b::bs)           => 
      val insertStrategy = diff(a::as,bs,c.insert(b))
      val deleteStrategy = diff(as,b::bs,c.delete(1))
      if (insertStrategy.weight <= deleteStrategy.weight)
        insertStrategy
      else
        deleteStrategy
  }
}

case class Annotations(annotations: List[Annotation] = Nil) extends AnyVal {
  override def toString = annotations.mkString(";")
  
  def positions(tpe: (AnnotationType.Value,String)): List[Int] = {
    val (_,result) = ((0,List.empty[Int]) /: annotations) {
      case ((offset,ps),Plain(n)) => (offset+n,ps)
      case ((offset,ps),Annotate(n,c)) =>
        if (c.contains(tpe)) (offset+n,offset::ps)
        else (offset+n,ps)
    }
    result
  }
  
  def annotate(n: Int, c: Set[(AnnotationType.Value,String)]): Annotations = {
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
  
  def ++ (a: Annotations): Annotations = {
    (annotations.lastOption, a.annotations.headOption) match {
      case (Some(Plain(n)),Some(Plain(m))) => Annotations(annotations.init ++ (Plain(n+m) +: a.annotations.tail))
      case (Some(Annotate(n,c)),Some(Annotate(m,d))) if c == d => Annotations(annotations.init ++ (Annotate(n+m,c) +: a.annotations.tail))
      case _ => Annotations(annotations ++ a.annotations)
    }
  }
  
  def length = annotations.map(_.length).reduceOption(_ + _).getOrElse(0)
  
  def compose(other: Annotations): Try[Annotations] = Annotations.compose(this,other)
  def transform(op: Operation): Try[Annotations] = Annotations.transform(this, op)
}

object Annotations {  
  private def addPlain(n: Int, as: List[Annotation]): List[Annotation] = as match {
    case Plain(m)::xs => Plain(n+m)::xs
    case xs if n > 0 => Plain(n)::xs
    case _ => as
  }
  
  private def addAnnotate(n: Int, c: Set[(AnnotationType.Value,String)], as: List[Annotation]): List[Annotation] = as match {
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
      case _ => Failure(new Exception("the annotation couldn't be transformed because it hasn't been applied to the same document as the operation"))
    }
    loop(a.annotations,o.actions,Nil).map(as => Annotations(as.reverse))
  }
  
  def compose(a: Annotations, b: Annotations): Try[Annotations] = {
    @tailrec
    def loop(as: List[Annotation], bs: List[Annotation], xs: List[Annotation]): Try[List[Annotation]] = (as,bs,xs) match {
      case (Nil,Nil,xs) => Success(xs)
      case (aa@(a::as),bb@(b::bs),xs) => (a,b) match {
        case (Plain(n),Plain(m)) => (n <=> m) match {
          case LT => loop(as,addPlain(m-n,bs),addPlain(n,xs))
          case EQ => loop(as,bs,addPlain(n,xs))
          case GT => loop(addPlain(n-m,as),bs,addPlain(m,xs))
        }
        case (Plain(n),Annotate(m,c)) => (n <=> m) match {
          case LT => loop(as,addAnnotate(m-n,c,bs),addAnnotate(n,c,xs))
          case EQ => loop(as,bs,addAnnotate(n,c,xs))
          case GT => loop(addPlain(n-m,as),bs,addAnnotate(m,c,xs))
        }
        case (Annotate(n,c),Plain(m)) => (n <=> m) match {
          case LT => loop(as,addPlain(m-n,bs),addAnnotate(n,c,xs))
          case EQ => loop(as,bs,addAnnotate(n,c,xs))
          case GT => loop(addAnnotate(n-m,c,as),bs,addAnnotate(m,c,xs))
        }
        case (Annotate(n,c),Annotate(m,c2)) => (n <=> m) match {
          case LT => loop(as,addAnnotate(m-n,c2,bs),addAnnotate(n,c ++ c2,xs))
          case EQ => loop(as,bs,addAnnotate(n,c ++ c2,xs))
          case GT => loop(addAnnotate(n-m,c,as),bs,addAnnotate(m,c ++ c2,xs))
        }
      }
      case _ => Failure(sys.error("the annotation lengths don't match!"))
    }
    loop(a.annotations, b.annotations, Nil).map(as => Annotations.apply(as.reverse))
  }
}