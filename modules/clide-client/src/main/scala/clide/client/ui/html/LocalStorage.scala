package clide.client.ui.html

import org.scalajs.dom.localStorage

object LocalStorage extends collection.mutable.Map[String,String] {  
  def get(key: String): Option[String] = {
    val r = localStorage.getItem(key)   
    if (r != null)
      Some(r.asInstanceOf[String])
    else
      None
  }
  
  def iterator = new Iterator[(String,String)] {
    var i = 0
    def hasNext() = i < localStorage.length
    def next() = {
      val r: (String,String) = (localStorage.key(i),localStorage.getItem(localStorage.key(i)).asInstanceOf[String])
      i += 1
      r
    }
  }
  
  def += (kv: (String, String)) = {
    localStorage.setItem(kv._1,kv._2)
    this
  }
  
  def -= (key: String) = {
    localStorage.removeItem(key)
    this
  }
  
  override def size: Int = localStorage.length.toInt
  
  override def clear() = localStorage.clear()
}