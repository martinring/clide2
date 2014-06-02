/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2014 Martin Ring                  **
**       | (__| | | (_| |  __/     http://clide.flatmap.net                   **
**        \___|_|_|\__,_|\___|                                                **
**                                                                            **
**   This file is part of Clide.                                              **
**                                                                            **
**   Clide is free software: you can redistribute it and/or modify            **
**   it under the terms of the GNU Lesser General Public License as           **
**   published by the Free Software Foundation, either version 3 of           **
**   the License, or (at your option) any later version.                      **
**                                                                            **
**   Clide is distributed in the hope that it will be useful,                 **
**   but WITHOUT ANY WARRANTY; without even the implied warranty of           **
**   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            **
**   GNU General Public License for more details.                             **
**                                                                            **
**   You should have received a copy of the GNU Lesser General Public         **
**   License along with Clide.                                                **
**   If not, see <http://www.gnu.org/licenses/>.                              **
\*                                                                            */

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
