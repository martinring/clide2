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

import clide.models._
import java.sql.Date
import java.security.MessageDigest
import scala.slick.lifted.MappedProjection

trait UserTables { this: Profile =>
  import profile.simple._

  class UserInfos(tag: Tag) extends Table[UserInfo with Password](tag, "users") {
    def name     = column[String]("name", O.PrimaryKey)
    def email    = column[String]("email")
    def password = column[Array[Byte]]("password")
    def *        = (name, email, password) <> (UserInfoWithPassword.tupled, UserInfoWithPassword.unapply)
  }
  
  val userInfos = TableQuery[UserInfos]
  
  object UserInfos {
    def get(name: String)(implicit session: Session) =
      userInfos.filter(_.name === name).firstOption

    def getAll(implicit session: Session) =
      userInfos.list

    def getByEmail(email: String)(implicit session: Session) =
      userInfos.filter(_.email === email).firstOption

    def authenticate(user: UserInfo with Password)(implicit session: Session) =
      userInfos.filter(_.name === user.name).filter(_.password === user.password).exists

    def insert(user: UserInfo with Password)(implicit session: Session) = {
      userInfos += user
    }
  }

  class LoginInfos(tag: Tag) extends Table[LoginInfo](tag, "logins") {
    def userName = column[String]("user")
    def key      = column[String]("key")
    def timeout  = column[Option[Date]]("timeout")
    def user     = foreignKey("fk_login_user", userName, userInfos)(_.name,
        ForeignKeyAction.Cascade, // update
        ForeignKeyAction.Cascade) // delete
    def isHuman  = column[Boolean]("isHuman")

    def *        = (userName, key, timeout, isHuman) <> (LoginInfo.tupled, LoginInfo.unapply)
  }
  
  val loginInfos = TableQuery[LoginInfos]
  
  object LoginInfos {
    def create(info: LoginInfo)(implicit session: Session) = {
      loginInfos += info
    }

    def getByUser(user: String)(implicit session: Session) =
      loginInfos.filter(_.userName === user).list

    def getByKey(key: String)(implicit session: Session) =
      loginInfos.filter(_.key === key).list

    def delete(login: LoginInfo)(implicit session: Session) =
      loginInfos.filter(_.key === login.key)
                .filter(_.userName === login.user)
                .delete
  }
}
