package clide.client.rx

trait Observer[-T] {
  def onNext(value: T): Unit
  def onError(error: Throwable): Unit
  def onCompleted(): Unit
}

object Observer {
  def apply[T](onNext: T=>Unit = (_:T)=>{}, 
               onError: Throwable=>Unit = (_:Throwable)=>{}, 
               onCompleted: ()=>Unit = ()=>{}) = {
    val n = onNext; val e = onError; val c = onCompleted
    new Observer[T] {
      def onNext(value: T) = n(value)
      def onError(error: Throwable) = e(error)
      def onCompleted() = c()
    }    
  }
}