package clide.persistence

import scala.slick.lifted.MappedTypeMapper
import clide.collaboration._
import clide.models._
import akka.serialization.SerializationExtension
import java.io.ByteArrayOutputStream
import java.io.ObjectOutputStream
import java.io.ByteArrayInputStream
import java.io.ObjectInputStream
import spray.json._
import spray.json.DefaultJsonProtocol._

trait Mappers {      
  implicit val ProjectAccessLevelMapper = 
    MappedTypeMapper.base[ProjectAccessLevel.Value, Int](_.id , ProjectAccessLevel.apply _)
      
  implicit val OperationMapper = {
    def serialize(op: Operation) = JsArray(op.actions.map {
      case Retain(n) => JsNumber(n)
      case Insert(s) => JsString(s)
      case Delete(n) => JsNumber(-n)
    }:_*).compactPrint
    
    def deserialize(s: String) = s.asJson match {
      case JsArray(s) => Operation(s.map {
        case JsString(s) => Insert(s)
        case JsNumber(n) if n < 0 => Delete(-n.toInt)
        case JsNumber(n) if n > 0 => Retain(n.toInt)
        case _ => sys.error("can't parse action")
      })
      case _ => sys.error("can't parse operation")
    }
    
    MappedTypeMapper.base[Operation, String](serialize,deserialize)
  }
}