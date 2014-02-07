package clide.client.rx

trait Subscription {
  def unsubscribe()
  def isUnsubscribed: Boolean
}

object Subscription {
  def apply(u: => Unit): Subscription = new Subscription {    
    private var unsubscribed = false
    def unsubscribe() { if (!unsubscribed) { unsubscribed = true; u } }
    def isUnsubscribed = unsubscribed
  }
  
  def apply(): Subscription = apply({})
}