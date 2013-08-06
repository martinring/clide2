package models.concurrency

import scala.collection.mutable.ArrayBuffer
import play.api.libs.json._
import play.api.libs.functional.syntax._

trait Operation { val char: Character }
case class Insert(char: Character, hint: Int) extends Operation
case class Hide(char: Character, hint: Int) extends Operation

object Operation {
  implicit val reads: Reads[Operation] = { 
    (JsPath \ "type").read[String] and
    (JsPath \ "ch").read[Character] and
    (JsPath \ "hint").read[Int]
  }.tupled.map {
    case ("insert",char,hint) => Insert(char,hint)
    case ("hide",char,hint)   => Hide(char,hint)
  }
  
  implicit val writes = new Writes[Operation] {
    def writes(op: Operation) = op match {
      case Insert(char,hint) => Json.obj(
          "type" -> "insert", 
          "ch" -> char,
          "hint" -> hint)
      case Hide(char,hint) => Json.obj(
          "type" -> "hide",
          "ch" -> char,
          "hint" -> hint)
    }
  }
}