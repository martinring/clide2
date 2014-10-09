package clide.reactive

import scala.concurrent.ExecutionContext
import scala.collection.mutable.Buffer

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
  def apply[A](event: Event[A])(implicit ec: ExecutionContext): HotPlate[A] = new HotPlate[A] {
    private val stop = event.stop _
    
    private var listeners = Buffer.empty[Channel[A]]
    
    private var latest = Option.empty[A]
    
    private def next(a: A) = {
      latest = Some(a)
      listeners.foreach(_.push(a))
    }
    
    private val close: Unit => Unit = { Unit =>
      latest = None
      listeners.foreach(_.close())
    }      
    
    def consume = {
      lazy val (out: Event[A], channel: Channel[A]) = 
        Event.broadcast[A](listeners -= channel)
      latest.foreach(channel.push(_))
      out
    }
    
    def dispose() = {
      listeners.foreach(_.close())
      listeners.clear()
      stop()
    }
    
    event.foreach(next)
         .foreach(close)
  }   
}