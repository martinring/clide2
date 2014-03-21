package scala.xml

object TopScope {
  
}

trait MetaData

object Null extends MetaData {
  
}

class Elem(prefix: String, 
           label: String, 
           attribs: MetaData, 
           scope: TopScope.type,
           minimizeEmpty: Boolean,
           child: Node*) {

}