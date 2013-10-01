package clide.persistence

import scala.slick.lifted.MappedTypeMapper
import clide.collaboration.Operation
import play.api.libs.json.Json
import clide.models._

trait Mappers {
  implicit val ProjectAccessLevelMapper = MappedTypeMapper.base[ProjectAccessLevel.Value, Int](
      _.id , ProjectAccessLevel.apply _)
      
  implicit val OperationMapper = MappedTypeMapper.base[Operation, String](
    Operation.Format.writes(_).toString , s => Operation.Format.reads(Json.parse(s)).get)         
}