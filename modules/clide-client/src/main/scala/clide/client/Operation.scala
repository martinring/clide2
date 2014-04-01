package clide.client

import scala.scalajs.js.annotation.JSExport
import scala.scalajs.js

@JSExport
class JsOperationWrapper(val op: clide.collaboration.Operation) {
  @JSExport 
  def toJSON = js.Array[js.Any](op.actions.map{
    case clide.collaboration.Retain(n) => n
    case clide.collaboration.Insert(s) => s
    case clide.collaboration.Delete(n) => -n
  })
  
  @JSExport
  def isNoop = op.actions.isEmpty || (op.actions.forall(_.isInstanceOf[clide.collaboration.Retain]))
  
  @JSExport
  def compose(b: JsOperationWrapper) =
    new JsOperationWrapper(clide.collaboration.Operation.compose(this.op, b.op).get)    
}

@JSExport
object Operation {
  @JSExport
  def actionType(action: js.Any): String = 
    js.typeOf(action).toString() match {
      case "number" => if (action.asInstanceOf[js.Number] > 0) "retain" else "delete"
      case "string" => "insert"
      case _ => "undefined"
    }
  
  @JSExport
  def fromJSON(actions: js.Array[js.Any]) =
    new JsOperationWrapper(
      new clide.collaboration.Operation(actions.toList.map { a =>
        actionType(a) match {
          case "retain" => clide.collaboration.Retain(a.asInstanceOf[js.Number].toInt)
          case "insert" => clide.collaboration.Insert(a.asInstanceOf[js.String])
          case "delete" => clide.collaboration.Delete(-a.asInstanceOf[js.Number].toInt)
        }
      })
    )
    
  @JSExport
  def transform(a: JsOperationWrapper, b: JsOperationWrapper) = {
    val (a_,b_) = clide.collaboration.Operation.transform(a.op, b.op).get
    (new JsOperationWrapper(a_), new JsOperationWrapper(b_))
  }
}