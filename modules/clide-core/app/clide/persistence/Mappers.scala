package clide.persistence

import scala.slick.lifted.MappedTypeMapper
import clide.collaboration.Operation
import clide.models._
import akka.serialization.SerializationExtension
import java.io.ByteArrayOutputStream
import java.io.ObjectOutputStream
import java.io.ByteArrayInputStream
import java.io.ObjectInputStream

trait Mappers {      
  implicit val ProjectAccessLevelMapper = 
    MappedTypeMapper.base[ProjectAccessLevel.Value, Int](_.id , ProjectAccessLevel.apply _)
      
  implicit val OperationMapper = 
    MappedTypeMapper.base[Operation, String](Operation.write,Operation.read)                 
}