package clide.reactive

import scala.concurrent.ExecutionContext
import scala.collection.mutable.Buffer

trait EventSource[A] {
  private val channels = Buffer.empty[Channel[A]]

  protected def trigger(event: A) = channels.foreach(_.push(event))
  protected def close() = channels.foreach(_.close())
  
  def listen(implicit ec: ExecutionContext): Event[A] = {
    lazy val (event: Event[A], channel: Channel[A]) = 
      Event.broadcast(channels -= channel)
    channels += channel
    event
  }
}