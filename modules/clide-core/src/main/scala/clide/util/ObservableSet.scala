package clide.util

import scala.reflect.ClassTag
import akka.actor._

object ObservableSet {
  case class Insert[T](t: T)
  case class Remove[T](t: T)
    
  case object Observe
  case object Ignore
  case class Inserted[T](t: T)
  case class Removed[T](t: T)
  
  def props[T](ordering: Ordering[T])(implicit tag: ClassTag[T]) = Props(classOf[ObservableSet[T]], ordering, tag)
}

class ObservableSet[T](ordering: Ordering[T])(implicit tag: ClassTag[T]) extends Actor {
  import ObservableSet._
  
  val observers = collection.mutable.Set.empty[ActorRef]
  val items = collection.mutable.SortedSet.empty[T](ordering) 
  
  def receive = {
    case Insert(t: T) => 
      if (items.add(t)) observers.foreach(_ ! Inserted(t))
    case Remove(t: T) =>
      if (items.remove(t)) observers.foreach(_ ! Removed(t))
    case Observe => 
      for (item <- items) sender ! Inserted(item)
      observers += sender
    case Ignore =>
      observers -= sender
  }
}