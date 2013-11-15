package clide.models

import java.sql.Date 

case class LoginInfo(
  user: String,
  key: String,
  timeout: Option[Date]
)

