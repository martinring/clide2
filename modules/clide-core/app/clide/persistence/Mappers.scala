package clide.persistence

import scala.slick.lifted.MappedTypeMapper
import clide.collaboration.Operation
import clide.models._

trait Mappers {
  implicit val ProjectAccessLevelMapper = 
    MappedTypeMapper.base[ProjectAccessLevel.Value, Int](_.id , ProjectAccessLevel.apply _)
      
  implicit val OperationMapper = 
    MappedTypeMapper.base[Operation, String](Operation.serialize, Operation.deserialize)            
}