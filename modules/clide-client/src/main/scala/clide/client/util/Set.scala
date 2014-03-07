package clide.client.util

/*
class Set[A] private[util] (private var buf: Buffer[A]) {
  def += (elem: A): Set.this.type = {
    if (!buf.contains(elem))
      buf += elem
    this
  }
  
  def -= (elem: A): Set.this.type = {
    buf -= elem
    this
  }
  
  def ++= (other: Buffer[A]): Set.this.type = {
    other.foreach(this += _)
    this
  }
  
  def contains(elem: A): Boolean = buf.contains(elem)
  
  def map[B](f: A => B): Set[B] = new Set(buf.map(f).distinct)    
}

object Set {
  def empty[A] = new Set(Buffer.empty)
}*/