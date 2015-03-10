//package clide.collaboration.trees
//
//import clide.collaboration.Operation
//
//
//sealed trait TOp
//
//case class SDelete(seq: String) extends TOp
//case class SUpdate(op: Operation[Char]) extends TOp
//case class SInsert(seq: String) extends TOp
//case class TDelete(tree: STree) extends TOp
//case class TUpdate(op: Map[String,TOp]) extends TOp
//case class TInsert(tree: STree) extends TOp
//
///*
//{
//  "files": {
//    "martin": {
//      "Seq.thy": {
//        "content": [4,"Hallo",-3]
//        "syntax": {
//          "command_0141358": {            
//            "end": 27
//            "tokens": {
//              "1": "files/martin/Seq.thy/#437-31"
//            }
//          }
//        }
//      }
//    }
//  }
//}
//*/
//
//object TOp {
//  def transform(op1: Map[String, TOp], op2: Map[String, TOp]): (Map[String, TOp], Map[String, TOp]) = {
//    val  = (op1.keySet intersect op2.keySet).map { key => (op1(key),op2(key)) match {
//      case (Delete,Delete)     => key -> Delete
//      case (Apply(a),Apply(b)) => Modify(Operation.transform(a,b).get)
//      case (Delete,Modify(op)) => key -> Apply(op)
//      case (Delete,Update(op)) => key -> Update(op)
//      case (_,Delete)          => key -> Delete
//      }
//    }.toMap
//  }
//  
//  def compose(op1: Map[String, TOp], op2: Map[String, TOp]): Map[String, TOp] = {
//    op1 ++ op2 ++
//    (op1.keySet intersect op2.keySet).map({ key => (op1(key),op2(key)) match {
//      case (_,Delete) => key -> Delete
//      case (Apply(a),Apply(b)) => key -> Apply(Operation.compose(a,b).get)
//      case (Update(a),Update(b)) => key -> Update(compose(a,b))
//      case (Delete,other) => key -> other
//      case (Update(a),Apply(b)) => sys.error("compose up mod")
//      case (Apply(a),Update(b)) => sys.error("compose mod up")      
//    }}).toMap
//  }
//}