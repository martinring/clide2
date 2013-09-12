package clide.actors

import play.api.libs.concurrent.Akka
import play.api.Play.current

object Infrastructure {
  var server = Akka.system.deadLetters
  var userServer = Akka.system.deadLetters
  var fileServer = Akka.system.deadLetters
  var projectServer = Akka.system.deadLetters
}