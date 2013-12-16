/*             _ _     _                                                      *\
**            | (_)   | |                                                     **
**         ___| |_  __| | ___      clide 2                                    **
**        / __| | |/ _` |/ _ \     (c) 2012-2013 Martin Ring                  **
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

import scala.slick.driver.ExtendedDriver
import scala.slick.jdbc.meta.MTable

class Schema(override val profile: ExtendedDriver) extends
  FileTables with ProjectTables with UserTables with Profile with Mappers {

  import profile.simple._

  val tables = Seq(
    UserInfos,
    ProjectInfos,
    FileInfos,
    LoginInfos,
    OpenedFiles,
    ProjectAccessLevels,    
    Revisions,
    SessionInfos)

  /** creates the tables, that don't exist already */
  def createAllIfNotExist()(implicit session: Session) {
    val ddls = for (table <- tables if !MTable.getTables.list.exists(_.name.name == table.tableName)) yield table.ddl
    if (ddls.nonEmpty) ddls.reduce(_++_).create
  }
  
  /** drops all existing tables */
  def dropAllIfExist()(implicit session: Session) {
    val ddls = for (table <- tables if MTable.getTables.list.exists(_.name.name == table.tableName )) yield table.ddl
    if (ddls.nonEmpty) ddls.reduce(_++_).drop
  }
}
