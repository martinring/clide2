package clide.client.ui.html

import scalajs.js

trait AttributeOwner

trait AttributeValueMapper[T] {
  def read(value: js.Dynamic): T
  def write(value: T): js.Dynamic
}

object AttributeValueMapper {
  implicit val stringMapper = new AttributeValueMapper[String] {
    def read(value: js.Dynamic): String = value.asInstanceOf[String]
    def write(value: String): js.Dynamic = value.asInstanceOf[js.Dynamic]
  }
}

abstract class Attribute[T,-E <: AttributeOwner](val name: String)(implicit mapper: AttributeValueMapper[T]) {
  private[html] def read(target: js.Dynamic): T = mapper.read(target.selectDynamic(name))
  private[html] def write(target: js.Dynamic, value: T): Unit = target.updateDynamic(name)(mapper.write(value))
}

trait Readable[T] { self: Attribute[T,_] => 
  def read(target: js.Dynamic): T = self.read(target)
}

trait Writable[T] { self: Attribute[T,_] => 
  def write(target: js.Dynamic, value: T): Unit = self.write(target, value)
}

object id extends Attribute[String]("id") with Readable[String] with Writable[String]