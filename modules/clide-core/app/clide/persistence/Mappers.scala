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
      
  implicit val OperationMapper = {
    def serialize(op: Operation): Array[Byte] = {
      val bytes = new ByteArrayOutputStream()
      val out   = new ObjectOutputStream(bytes)
      out.writeObject(op)
      bytes.toByteArray
    }
    def deserialize(bytes: Array[Byte]) = {
      val stream = new ByteArrayInputStream(bytes)
      val in     = new ObjectInputStream(stream)
      in.readObject().asInstanceOf[Operation]
    }
    MappedTypeMapper.base[Operation, Array[Byte]](serialize,deserialize)
  }                 
}