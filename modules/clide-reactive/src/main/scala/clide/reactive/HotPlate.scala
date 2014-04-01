package clide.reactive

import scala.concurrent.ExecutionContext

/**
 * A `HotPlate` keeps an `Event` hot. This means that it subscribes to the event until the HotPlate 
 * itself is disposed. It's main purpose is to serve as a multiplexer as it takes the responsibility 
 * for the cancellation of the underlying event.
 */
trait HotPlate[+A] {
  def consume: Event[A]
  def dispose()
}

object HotPlate {
  /**
   * Creates a HotPlate for the given Event.
   */
  def apply[A](event: Event[A])(implicit ec: ExecutionContext): HotPlate[A] = ??? // TODO!!!   
}