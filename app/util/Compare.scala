package util {
  package object compare {
	trait ORD
	object LT
	object GT
	object EQ
	  
	implicit class Compare[T <% Ordered[T]](t: T) {
	  def <=>(other: T) = t.compareTo(other) match {
	    case 0 => EQ
	    case n if n < 0 => LT
	    case _ => GT
	  }
	} 
  }
}