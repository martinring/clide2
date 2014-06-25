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

package clide.models

import java.security.MessageDigest
import java.util.Arrays

@SerialVersionUID(1L)
case class UserInfo(
    name: String,
    email: String) {
  def withPassword(plain: String) = { // TODO: Think about security
    new UserInfo(name,email) with Password {
      val password = UserInfo.passwordHash(name,plain)
    }
  }
}

object UserInfo {
  def passwordHash(name: String, password: String) =
    MessageDigest.getInstance("MD5").digest((name + password).getBytes("UTF-8"))
}

object UserInfoWithPassword {
  def apply(name: String, email: String, pword: Array[Byte]) =
    new UserInfo(name,email) with Password { val password = pword }

  def unapply(u: UserInfo with Password) = Some((u.name,u.email,u.password))
  
  val tupled = (apply _).tupled
}

trait Password { self: UserInfo =>
  val password: Array[Byte]
  def authenticate(password: String) = Arrays.equals(UserInfo.passwordHash(name, password),this.password)
}
