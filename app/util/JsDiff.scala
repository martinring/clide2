package util

import play.api.libs.json._

/**
 * Provides diff for JSON.
 */
object JsDiff {
  def apply(a: JsValue, b: JsValue): String = (a,b) match {
    // for now we just return b... but this leaves room for
    // bandwidth and performance optimizations in the future
    case (a, b) => f"function(a){return ${b.toString}}"    
  }
}