package clide.client.rx

trait Location
object Head extends Location
object Last extends Location
object NoLoc extends Location
case class Index(n: Int) extends Location

trait CollectionChange[A]
case class Insert[A](loc: Location, elem: A) extends CollectionChange[A]
case class Remove[A](loc: Location, elem: A) extends CollectionChange[A]
case class Update[A](loc: Location, elem: A) extends CollectionChange[A]

trait ObservableCollection[A] extends Observable[CollectionChange[A]]