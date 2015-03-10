package clide.collaboration.experimental

import scala.annotation.tailrec

sealed trait Reactive[T] {
  protected var value: T
  
  protected val ops: Operations[T]
  
  protected var diff: ops.Operation = ops.noop
  
  def modify(op: ops.Operation) = {
    value = ops.applyOp(op, value)
    diff = ops.compose(diff, op)
    op
  }
  
  def getDiff(): ops.Operation = {
    val result = diff
    diff = ops.noop
    diff
  }
  
  implicit def get = value
}

trait Bijection[A,B] {  
  val aops: Operations[A]
  val bops: Operations[B]
  
  def forth(operation: aops.Operation): bops.Operation
  def back(operation: bops.Operation): aops.Operation
}

object Bijection {
  def apply[A,B](a: Operations[A], b: Operations[B])
    (f: a.Operation => b.Operation)
    (g: b.Operation => a.Operation) = new Bijection[A,B] {
    val aops = a
    val bops = b
    def forth(op: aops.Operation) = f(op.asInstanceOf[a.Operation]).asInstanceOf[bops.Operation]
    def back(op: bops.Operation) = g(op.asInstanceOf[b.Operation]).asInstanceOf[aops.Operation]
  }
}

class Rational private[experimental] (val numerator: Int, val denominator: Int) {
  def unary_- = new Rational(-numerator,denominator)
  
  def reciprocal = new Rational(denominator,numerator)
  
  def +(that: Rational) = Rational(
    this.numerator * that.denominator + that.numerator * this.denominator,
    this.denominator * that.denominator)
    
  def *(that: Rational) = Rational(
    this.numerator * that.numerator,
    this.denominator * that.denominator)
}

object Rational {    
  def gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)
  
  def apply(numerator: Int, denominator: Int) = {
    val gcd = this.gcd(numerator, denominator)
    new Rational(numerator / gcd, denominator / gcd)
  }
}

case class RRational(protected var value: Rational) extends Reactive[Rational] {
  protected val ops = RRational
  def +=(other: Rational) = modify(ops.plus(other))
  def -=(other: Rational) = modify(ops.plus(-other))
  def *=(other: Rational) = modify(ops.times(other))
  def /=(other: Rational) = modify(ops.times(other.reciprocal))
}

sealed trait Operations[A] {
  type Operation   
  def compose(a: Operation, b: Operation): Operation
  def transform(a: Operation, b: Operation): (Operation,Operation)
  def inverse(a: Operation): Operation
  def applyOp(op: Operation, a: A): A
  def noop: Operation
}

object RRational extends Operations[Rational] {
  case class ROp(times: Rational, plus: Rational) {
    def plus(value: Rational): ROp = ROp(times, plus + value)
    def times(value: Rational): ROp = ROp(times * value, plus * value)
    def inverse: ROp = ROp(times.reciprocal, -(plus * times.reciprocal))
  }   
  
  type Operation = ROp
  
  def noop = ROp(Rational(1,1),Rational(0,1))
    
  def plus(value: Rational): Operation = ROp(Rational(1,1),value)
  def times(value: Rational): Operation = ROp(value,Rational(0,1)) 
  
  def compose(a: Operation, b: Operation): Operation = 
    a.times(b.times).plus(b.plus)
  
  def transform(a: Operation, b: Operation): (Operation, Operation) = 
    (a.times(b.times.reciprocal).plus(-b.plus),
     b.times(a.times.reciprocal).plus(-a.plus))
    
  def applyOp(op: Operation, a: Rational): Rational =
    (a * op.times) + op.plus
    
  def inverse(op: Operation): Operation = op.inverse
}

class RReplace[T] extends Operations[Option[T]] {  
  case class Replace(prev: Option[T], next: Option[T])
  
  type Operation = Replace
  
  def noop = Replace(None,None)
  
  def compose(a: Operation, b: Operation): Operation =
    Replace(a.prev,b.next)
    
  def transform(a: Operation, b: Operation): (Operation,Operation) =
    (Replace(b.next,a.next),Replace(a.next,b.next))
  
  def applyOp(op: Operation, a: Option[T]): Option[T] = op.next
          
  def inverse(op: Operation): Operation = 
    Replace(op.next,op.prev)
}

/*class RRecord[A] extends Operations[Product] {
  class Field(private var value: T) {
    
  }
  
  def field[T](initialValue: T)(operations: Operations[T]) = {
  }
  
  def inverse(op: Operation): Operation = 
}

case class Person(name: String, age: Int)

object Person extends RRecord[Person] {
  val name = field(Option.empty[String])(new RReplace[String])
}*/