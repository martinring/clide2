package clide.db

/**
 * A GenericUser can either be a real human user (i.e. User) or some connected system,
 * that (ideally) aids the human users in their work. 
 */
trait GenericUser {
  val name: String
}