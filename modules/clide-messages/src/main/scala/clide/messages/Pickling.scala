package clide.messages

import org.scalajs.spickling._

object Pickling {
  implicit object ConsPickler extends Pickler[::[Any]] {
    def pickle[P](value: ::[Any])(implicit registry: PicklerRegistry,
        builder: PBuilder[P]): P = {
      builder.makeArray(value.map(registry.pickle(_)): _*)
    }
  }

  implicit object ConsUnpickler extends Unpickler[::[Any]] {
    def unpickle[P](pickle: P)(implicit registry: PicklerRegistry,
        reader: PReader[P]): ::[Any] = {
      val len = reader.readArrayLength(pickle)
      assert(len > 0)
      ((0 until len).toList map { index =>
        registry.unpickle(reader.readArrayElem(pickle, index))
      }).asInstanceOf[::[Any]]
    }
  }
  
  def init() = {
    PicklerRegistry.register(Nil)
    PicklerRegistry.register[::[Any]]
    
    PicklerRegistry.register[Auth.Login]
    PicklerRegistry.register[Auth.LoggedIn]
    PicklerRegistry.register[Auth.SignUp]
    
    PicklerRegistry.register(User.GetProjectInfos)
    PicklerRegistry.register[User.ProjectInfos]
  }
}