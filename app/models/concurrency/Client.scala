package models.concurrency

/**
 * This implementation is based on the WOOT concept introduced
 * in "RT groupware without OT" by Oster et al. (2005)
 * As an extension we work with position hints in operations: 
 * since characters can not be deleted we can always be sure that
 * an operation can only be shifted into one direction (i.e. forward)
 * @author Martin Ring <martin.ring@dfki.de>
 */
class Client(id: Int, doc: Document) {  
  var clock = 0  
  
  def generateId() = {
    clock += 1
    Server.maxClients * clock + id    
  }
  
  def applyOperation: PartialFunction[Operation,Unit] = new PartialFunction[Operation,Unit] {
    def isDefinedAt(op: Operation) = op match {
      case Insert(char,hint) => doc.indexOf(char.previous,hint) >= 0 &&
                                doc.indexOf(char.next,hint) >= 0                                
      case Hide(char,hint)   => doc.indexOf(char.id, hint) >= 0
    }
    
    def apply(op: Operation) = op match {
      case Insert(char,hint) => 
        def integrate(c: Character, p: Long, n: Long): Unit = {
	      val pi = doc.indexOf(p,hint)
	      val ni = doc.indexOf(n,hint)
	      if (pi+1==ni) doc.insert(char,ni)
	      else {
	        val s = doc.subseq(pi,ni)
	        val l = doc(pi) +: s.filter(c => !s.exists(c2 => c2.id == c.next || c2.id == c.previous)) :+ doc(ni)
	        val i = l.indexWhere(c => c.id >= char.id)
	        val np = l(i-1).id
	        val nn = l(i).id
	        require(np != p || nn != n)
	        integrate(char,np,nn)
	      }
        }
        integrate(char, char.previous, char.next)
      case Hide(char,hint)   => doc(doc.indexOf(char.id, hint)).visible = false
    }
  }
  
  def generateInsert(position: Int, character: Char) = {
    val cp = doc.visible.lift(position).getOrElse(doc.start)
    val cn = doc.visible.lift(position+1).getOrElse(doc.end)
    val c = new Character(generateId(),character,cp.id,cn.id,true)
    Insert(c,doc.indexOf(cp.id, position))
  }
  
  def generateHide(position: Int) = {
    val c = doc.visible(position)
    Hide(c,doc.indexOf(c.id, position))  
  }
}