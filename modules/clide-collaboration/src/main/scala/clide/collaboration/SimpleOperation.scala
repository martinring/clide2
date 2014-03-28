package clide.collaboration

object SimpleOperation {

def map[A, B](f: A => B, x1: Option[A]): Option[B] = (f, x1) match {
  case (f, Some(x)) => Some[B](f(x))
  case (f, None) => None
}

abstract sealed class action[A]
final case class Retain[A]() extends action[A]
final case class Insert[A](a: A) extends action[A]
final case class Delete[A]() extends action[A]

def deletea[A](x0: List[action[A]]): List[action[A]] = x0 match {
  case Insert(c) :: next => Insert[A](c) :: deletea[A](next)
  case Nil => List(Delete[A]())
  case Retain() :: va => Delete[A]() :: Retain[A]() :: va
  case Delete() :: va => Delete[A]() :: Delete[A]() :: va
}

def compose[A](x0: List[action[A]], bs: List[action[A]]):
      Option[List[action[A]]] =
  (x0, bs) match {
  case (Nil, Nil) => Some[List[action[A]]](Nil)
  case (Delete() :: as, bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => deletea[A](a),
                           compose[A](as, bs))
  case (Nil, Insert(c) :: bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => Insert[A](c) :: a,
                           compose[A](Nil, bs))
  case (Retain() :: va, Insert(c) :: bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => Insert[A](c) :: a,
                           compose[A](Retain[A]() :: va, bs))
  case (Insert(vb) :: va, Insert(c) :: bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => Insert[A](c) :: a,
                           compose[A](Insert[A](vb) :: va, bs))
  case (Retain() :: as, Retain() :: bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => Retain[A]() :: a,
                           compose[A](as, bs))
  case (Retain() :: as, Delete() :: bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => deletea[A](a),
                           compose[A](as, bs))
  case (Insert(c) :: as, Retain() :: bs) =>
    map[List[action[A]],
         List[action[A]]]((a: List[action[A]]) => Insert[A](c) :: a,
                           compose[A](as, bs))
  case (Insert(uu) :: as, Delete() :: bs) => compose[A](as, bs)
  case (Retain() :: va, Nil) => None
  case (Insert(vb) :: va, Nil) => None
  case (Nil, Retain() :: va) => None
  case (Nil, Delete() :: va) => None
}

def transform[A](x0: List[action[A]], bs: List[action[A]]):
      Option[(List[action[A]], List[action[A]])] =
  (x0, bs) match {
  case (Nil, Nil) => Some[(List[action[A]], List[action[A]])]((Nil, Nil))
  case (Insert(c) :: as, bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, bt):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (Insert[A](c) :: at, Retain[A]() :: bt)
                               },
                              transform[A](as, bs))
  case (Nil, Insert(c) :: bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, bt):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (Retain[A]() :: at, Insert[A](c) :: bt)
                               },
                              transform[A](Nil, bs))
  case (Retain() :: va, Insert(c) :: bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, bt):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (Retain[A]() :: at, Insert[A](c) :: bt)
                               },
                              transform[A](Retain[A]() :: va, bs))
  case (Delete() :: va, Insert(c) :: bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, bt):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (Retain[A]() :: at, Insert[A](c) :: bt)
                               },
                              transform[A](Delete[A]() :: va, bs))
  case (Retain() :: as, Retain() :: bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, bt):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (Retain[A]() :: at, Retain[A]() :: bt)
                               },
                              transform[A](as, bs))
  case (Delete() :: as, Delete() :: bs) => transform[A](as, bs)
  case (Retain() :: as, Delete() :: bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, bt):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (at, Delete[A]() :: bt)
                               },
                              transform[A](as, bs))
  case (Delete() :: as, Retain() :: bs) =>
    map[(List[action[A]], List[action[A]]),
         (List[action[A]],
           List[action[A]])]((a: (List[action[A]], List[action[A]])) =>
                               {
                                 val (at, aa):
                                       (List[action[A]], List[action[A]])
                                   = a;
                                 (Delete[A]() :: at, aa)
                               },
                              transform[A](as, bs))
  case (Retain() :: va, Nil) => None
  case (Delete() :: va, Nil) => None
  case (Nil, Retain() :: va) => None
  case (Nil, Delete() :: va) => None
}

} /* object SimpleOperation */
