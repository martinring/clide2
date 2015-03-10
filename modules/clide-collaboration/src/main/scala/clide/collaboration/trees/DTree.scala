//package clide.collaboration.trees
//
//trait BTree[A] { outer =>
//  def get: () => A
//  def set: A => Unit
//    
//  def map[B](f: A => B, g: B => A): BTree[B] = new BTree[B] {
//    def get: () => B = () => f(outer.get())
//    def set: B => Unit = b => outer.set(g(b))
//  }
//  
//  def flatMap[B](f: A => BTree[B], g: B => BTree[A]): BTree[B] = new BTree[B] {
//    def get: () => B = f(outer.get()).get
//    def set: B => Unit = b => outer.set(g(b).get())
//  }
//}
//
//object BVar {
//  def apply[A](init: A) = new BTree[A] {
//    private var value = init
//    def get = () => value
//    def set = x => value = x
//  }
//}
//
//object BTree {
//  implicit class BNum(ta: BTree[Double]) {
//    def <+(tb: BTree[Double]) = new BTree[Double] {
//      def get = () => ta.get() + tb.get()
//      def set = x => tb.set(x - ta.get())
//    }
//    
//    def +>(tb: BTree[Double]) = new BTree[Double] {
//      def get = () => ta.get() + tb.get()
//      def set = x => ta.set(x - tb.get())
//    }
//    
//    def <*(tb: BTree[Double]) = new BTree[Double] {
//      def get = () => ta.get() * tb.get()
//      def set = x => tb.set(x / tb.get())
//    }
//  }
//  
//  implicit class BMap[K,V](ta: BTree[Map[K,V]]) {
//    def select(key: K) = new BTree[Option[V]] {
//      def get = () => ta.get().get(key)
//      def set = x => x.fold
//        (ta.set(ta.get() - key))
//        ((x: V) => ta.set(ta.get().updated(key, x)))
//    }
//  }
//  
//  implicit class BSeq[A](ta: BTree[Seq[A]]) {
//    
//  }
//}
//
//object Test {
//  BVar(Map("Hallo" -> 5.0))
//}