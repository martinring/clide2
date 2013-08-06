package models.concurrency

import scala.collection.mutable.ArrayBuffer

class Document {       
  val start: Character = new Character(0,'\0',Server.maxClients,Server.maxClients,false)
  val end: Character   = new Character(Server.maxClients,'\0',0,0,false)
  private val sequence: ArrayBuffer[Character] = ArrayBuffer(start,end)  
  
  def length: Int           = sequence.length
  def apply(position: Int)  = sequence.apply(position)
  def iterator              = sequence.iterator
  def indexOf(c: Long, hint: Int = 0): Int = hint match {
    case 0 => sequence.indexWhere(e => e.id == c)
    case n => (n to length).find{ case i: Int => sequence(i) == c }.getOrElse(-1)
  }       
  def insert(c: Character, p: Int) = sequence.insert(p,c)  
  def subseq(s: Int, e: Int) = sequence.view(s+1,e)
  def contains(c: Character) = sequence.contains(c)
  
  def visible: Stream[Character] = sequence.toStream.filter{ case c: Character => c.visible }
  def value = visible.map{ case c: Character => c.value }
  
  override def toString = value.mkString    
}
