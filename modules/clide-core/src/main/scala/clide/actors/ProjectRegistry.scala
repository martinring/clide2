package clide.actors

import akka.actor._

private[actors] object ProjectRegistry {
  def props = Props(classOf[ProjectRegistry])
}

private class ProjectRegistry private () extends Actor {
  
  
  def receive = {
    case _ =>
  }
}