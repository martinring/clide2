package clide.reactive

import scala.concurrent.ExecutionContext

trait HotPlate[+A] {
  def consume: Event[A]
  def dispose()
}

object HotPlate {
  def apply[A](event: Event[A])(implicit ec: ExecutionContext): HotPlate[A] = ??? // TODO!!!   
}