package clide.client.ui

import scalajs.js
import scala.language.implicitConversions
import clide.client.rx._

trait AttributeValueMapper[T] {
  def read(value: String): T
  def write(value: T): String
}

object AttributeValueMapper {
  implicit object StringAttributeValueMapper extends AttributeValueMapper[String] {
    def read(value: String) = value
    def write(value: String) = value
  }
  
  implicit object BooleanAttributeValueMapper extends AttributeValueMapper[Boolean] {
    def read(value: String) = value == "true"
    def write(value: Boolean) = if (value) "true" else "false"
  }
}

abstract class Attribute[T,-N <: HtmlNodeType](val name: String)(implicit mapper: AttributeValueMapper[T]) {
  def get(elem: js.Dynamic): T =
    mapper.read(elem.selectDynamic(name).asInstanceOf[String])
    
  def set(elem: js.Dynamic, value: T) = 
    elem.updateDynamic(name)(mapper.write(value))
    
  def := (v: T) = new UsedAttribute[N] { 
    def attach(elem: js.Dynamic) = set(elem,v)
  }
  
  def refresh(elem: EventTarget): Option[Observable[Unit]] = None
  
  def --> (v: TemplateVar[T]) = new UsedAttribute[N] {
    def attach(elem: js.Dynamic) = {
      refresh(elem.asInstanceOf[EventTarget]).foreach(_.subscribe(Observer(_ => v.refresh)))
      v.getter = Some(() => get(elem))
    }
  }
  
  def <-- (v: Observable[T]) = new UsedAttribute[N] {
    def attach(elem: js.Dynamic) = v.subscribe(Observer(v => set(elem, v)))
  }
  
  def <--> (v: TemplateVar[T]) = new UsedAttribute[N] {
    def attach(elem: js.Dynamic) = {}
  }
}

trait UsedAttribute[-E <: HtmlNodeType] { 
  def attach(elem: js.Dynamic)
  def detach(elem: js.Dynamic) = { }
}

object accessKey extends Attribute[String,NodeType]("accessKey")
object className extends Attribute[String,NodeType]("className")
object contentEditable extends Attribute[Boolean,NodeType]("contentEditable")
object hidden extends Attribute[Boolean,NodeType]("hidden")
object id extends Attribute[String,NodeType]("id")
object title extends Attribute[String,NodeType]("title")
object lang extends Attribute[String,NodeType]("lang")
object translate extends Attribute[Boolean,NodeType]("translate")
object value extends Attribute[String,InputNodeType]("value") {
  override def refresh(target: EventTarget) = Some(Observable.fromEvent(target, "input").map(_ => ()))
}
object inputType extends Attribute[String,InputNodeType]("type")

trait NodeFactory {
  def create(): js.Dynamic
}

object NodeFactory {
  implicit def textFactory(value: String) = new NodeFactory {
    def create() = document.createTextNode(value).asInstanceOf[js.Dynamic]
  }  
  
  implicit def textObserverFactory(value: Observable[String]) = new NodeFactory {
    def create() = {
      val elem = document.createTextNode("")
      value.subscribe(Observer(elem.textContent = _))
      elem.asInstanceOf[js.Dynamic]
    }
  }
  
  implicit def switch(value: Observable[NodeFactory]) = new NodeFactory {    
    def create() = {
      val elem = document.createDocumentFragment()
      var node = document.createComment("uninitialized").asInstanceOf[HTMLElement]
      elem.appendChild(node)
      value.subscribe(Observer{
        factory =>          
          val newNode = factory.create().asInstanceOf[HTMLElement]
          if (node.parentElement == null)
            elem.replaceChild(newNode, node)
          else 
            node.parentElement.replaceChild(newNode, node)
          node = newNode
      })
      elem.asInstanceOf[js.Dynamic]
    }
  }
}

case class TemplateVar[T](default: T) extends Observable[T] {
  private var subscribers = Set.empty[Observer[T]]
  
  private var cache: Option[T] = None
  
  private[ui] var getter: Option[() => T] = None
  
  private[ui] def refresh = {
    val next = get
    if (!cache.exists(_ == next)) {
      subscribers.foreach(_.onNext(get))
      cache = Some(next)
    }
  }
  
  def subscribe(obs: Observer[T]) = {
    subscribers += obs    
    obs.onNext(get)    
    Subscription(subscribers -= obs)
  }
  
  def get = getter.map(_()).getOrElse(default)  
}

abstract class TagFactory[+T <: NodeType](name: String, defaults: UsedAttribute[T]*) {
  def apply(attributes: UsedAttribute[T]*)(children: NodeFactory*): NodeFactory = new NodeFactory {
    def create() = {
      val elem = document.createElement(name)
      attributes.foreach(_.attach(elem.asInstanceOf[js.Dynamic]))
      children.foreach { child =>
        elem.appendChild(child.create().asInstanceOf[HTMLElement])
      }
      elem.asInstanceOf[js.Dynamic]
    }    
  }
}

object Header extends TagFactory[DivNodeType]("header")
object Footer extends TagFactory[DivNodeType]("footer")
object Article extends TagFactory[DivNodeType]("article")
object Section extends TagFactory[DivNodeType]("section")
object Nav extends TagFactory[DivNodeType]("nav")
object Div extends TagFactory[DivNodeType]("div")
object Span extends TagFactory[NodeType]("span")
object TextBox extends TagFactory[InputNodeType]("input",inputType := "text")
object PasswordBox extends TagFactory[InputNodeType]("input",inputType := "password")
object Button extends TagFactory[ButtonNodeType]("button")
object OrderedList extends TagFactory[OListNodeType]("ol")
object UnorderedList extends TagFactory[UListNodeType]("ul")
object DescriptionList extends TagFactory[DListNodeType]("dl")