package clide.persistence

import scala.slick.driver.ExtendedDriver

object Database extends FileTables with ProjectTables with UserTables with Profile with Mappers {
  override val profile: ExtendedDriver = slick.driver.H2Driver
}