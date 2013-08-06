package models.concurrency

import play.api.libs.json._
import play.api.libs.functional.syntax._

class Character(
  val id: Long,
  val value: Char,  
  val previous: Long,
  val next: Long,
  var visible: Boolean = true
) { 
  override def equals(other: Any) = other match {
    case c: Character if c.id == this.id => true
    case id: Long if id == this.id => true
    case _ => false
  }  
}

object Character {
  implicit val reads: Reads[Character] = {
    (JsPath \ "id").read[Long] and
    (JsPath \ "value").read[String] and
    (JsPath \ "previous").read[Long] and
    (JsPath \ "next").read[Long]
  }.tupled.map{ case (id,v,p,n) => new Character(id,v.head,p,n) }
  
  implicit val writes: Writes[Character] = new Writes[Character] {
    def writes(c: Character) = Json.obj(
	  "id" -> c.id,
	  "value" -> c.value.toString,
	  "previous" -> c.previous,
	  "next" -> c.next        
    )
  } 
    
}