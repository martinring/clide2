package clide.actors

import play.api.libs.concurrent.Akka
import play.api.Play.current

object Infrastructure {
  var userServer = Akka.system.deadLetters
}