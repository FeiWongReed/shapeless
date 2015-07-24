package shapeless

/**
 * Wraps a `T` made of implicit values.
 *
 * E.g. looking for an implicit `Implicit[A :: B :: HNil]`, will
 * look up for implicits `A` and `B`. If both are found, it succeeds and the implicit
 * `A` and `B` are available via `value`. Same thing for longer HLists.
 *
 * Looking for an `Implicit[A :+: B :+: CNil]` will look up for an implicit `A` first,
 * else for an implicit `B` if it fails. If either one of them is found, it is
 * available wrapped in a `A :+: B :+: CNil`, via `value`. Same thing with longer coproducts.
 *
 * One can also look for types having a `Generic` instance. Their generic representation
 * will be looked up as above, then converted to the right type with `Generic`.
 *
 * Example:
 *     def func[T](t: T)
 *      (implicit impl: Implicit[
 *        ColumnPrint[T] :+:
 *        PrettyPrint[T] :+:
 *        Show[T] :+: CNil
 *      ]) = ???
 * will look up for a `ColumnPrint[T]` first. If not found, for a `PrettyPrint[T]`.
 * If not found, for a `Show[T]`. The first found implicit is wrapped in the above
 * coproduct, then in `Implicit`.
 *
 */
trait Implicit[T] {
  def value: T
}

trait LowPriorityImplicit {
  /** Low priority Implicit for coproducts - look up for an Implicit instance for the tail. */
  implicit def cconsTailLookup[H, T <: Coproduct]
   (implicit
     tail: Strict[Implicit[T]]
   ): Implicit[H :+: T] =
    Implicit.mkImplicit(Inr(tail.value.value))
}

object Implicit extends LowPriorityImplicit {
  def apply[T](implicit imp: Implicit[T]): Implicit[T] = imp

  def mkImplicit[T](t: => T): Implicit[T] =
    new Implicit[T] {
      def value = t
    }

  /** Implicit of empty HList - always succeeds (equivalent to looking for no particular implicit, this cannot fail.) */
  implicit val hnilLookup: Implicit[HNil] =
    mkImplicit(HNil)

  /** Implicit of non-empty HList - succeeds if an implicit head is found, and an instance of `Implicit` for the tail too. */
  implicit def hconsLookup[H, T <: HList]
   (implicit
     head: Strict[H],
     tail: Strict[Implicit[T]]
   ): Implicit[H :: T] =
    mkImplicit(head.value :: tail.value.value)

  /** Higher priority coproduct Implicit instance - succeeds if an implicit head is found. */
  implicit def cconsHeadLookup[H, T <: Coproduct]
   (implicit
     head: Strict[H]
   ): Implicit[H :+: T] =
    mkImplicit(Inl(head.value))

  implicit def genericLookup[F, G]
   (implicit
     gen: Generic.Aux[F, G],
     underlying: Lazy[Implicit[G]]
   ): Implicit[F] =
    mkImplicit(gen.from(underlying.value.value))
}

