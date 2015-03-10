//package clide.client
//
//import scala.scalajs.js
//
//trait JSONEngine[T] {
//  trait ApplyUnapply[U] {
//    def apply(value: U): T
//    def unapply(json: T): Option[U]
//  }
//  
//  val Null: ApplyUnapply[Null]
//  val Boolean: ApplyUnapply[Boolean]
//  val String: ApplyUnapply[String]
//  val Number: ApplyUnapply[Double]
//  val Object: ApplyUnapply[Map[String,T]]
//  val Array: ApplyUnapply[Seq[T]]
//}
//
//object NativeJSONEngine extends JSONEngine[js.Any] {
//  val Null = new ApplyUnapply[Null] {
//    def apply(value: Null): js.Any = null
//    def unapply(value: js.Any): Option[Null] =
//      if (value == null) Some(null) 
//      else None
//  }
//  
//  val Boolean = new ApplyUnapply[Boolean] {
//    def apply(value: Boolean): js.Any = value
//    def unapply(value: js.Any): Option[Boolean] =
//      if (js.typeOf(value) == "boolean") Some(value.asInstanceOf[js.Boolean])
//      else None
//  }
//  
//  val String = new ApplyUnapply[String] {
//    def apply(value: String): js.Any = value
//    def unapply(value: js.Any): Option[String] =
//      if (js.typeOf(value) == "string") Some(value.asInstanceOf[js.String])
//      else None
//  }
//  
//  val Number = new ApplyUnapply[Double] {
//    def apply(value: Double): js.Any = value
//    def unapply(value: js.Any): Option[Number] =
//      if (js.typeOf(value) == "number") Some(value.asInstanceOf[js.Number])
//      else None
//  }
//  
//  val Object = new ApplyUnapply[Map[String,js.Any]] {
//    def apply(value: Map[String,js.Any]): js.Any = 
//      js.Dictionary.apply(value.toSeq :_*)
//    def unapply(value: js.Any): Option[Map[String,js.Any]] = 
//      if (js.typeOf(value) == "object") Some(new Map[String,js.Any] {
//        def get(key: String) = value.asInstanceOf[js.Dictionary[js.Any]].get(key).toOption
//        def iterator: Iterator[(String,js.Any)] = value.asInstanceOf[js.Dictionary[js.Any]].iterator
//        def +(kv: (String, js.Any)) = 
//      })
//      else None
//  }
//}
