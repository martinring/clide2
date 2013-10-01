package clide.persistence

import scala.slick.lifted.MappedTypeMapper
import clide.models._

trait Mappers {
  implicit val AccessLevelMapper = MappedTypeMapper.base[AccessLevel.Value, Int](
    _.id , AccessLevel.apply _)
}