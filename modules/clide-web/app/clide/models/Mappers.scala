package clide.models

import scala.slick.lifted.MappedTypeMapper
import clide.collaboration.Operation
import play.api.libs.json.Json

object Mappers {
  implicit val ProjectAccessLevelMapper = MappedTypeMapper.base[ProjectAccessLevel.Value, Int](
      _.id , ProjectAccessLevel.apply _)
      
  implicit val OperationMapper = MappedTypeMapper.base[Operation, String](
    Operation.SourceOperationFormat.writes(_).toString , s => Operation.SourceOperationFormat.reads(Json.parse(s)).get)         
}