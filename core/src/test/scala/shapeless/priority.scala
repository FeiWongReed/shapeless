package shapeless

import Definitions._

import scala.language.reflectiveCalls
import scala.collection.generic.CanBuildFrom
import org.junit.Test


object Definitions {

  case class CC1(i: Int)
  case class CC2(i: Int)

  case class CC3(i1: Int, i2: Int)
  case class CC4(d: Double)
  case class CC5(l: List[Double])
  case class CC6(n: Double, l: List[Double])

  sealed trait Tree0
  object Tree0 {
    case class Node(left: Tree0, right: Tree0, v: Int) extends Tree0
    case object Leaf extends Tree0
  }

  sealed trait Tree
  object Tree {
    case class Node(left: Tree, right: Tree, v: Int) extends Tree
    case object Leaf extends Tree

    // Not always found if put in Leaf (is this expected?)
    implicit val tc: TC[Leaf.type] = TC.of[Leaf.type](_ => "Leaf")
    implicit val tc0: TC0[Leaf.type] = TC0.of[Leaf.type](_ => "Leaf")
  }

  trait TC[T] {
    def msg(n: Int): String
  }

  object TC {
    def apply[T](implicit tc: TC[T]): TC[T] = tc

    def of[T](msg0: Int => String): TC[T] =
      new TC[T] {
        def msg(n: Int) = if (n >= 0) msg0(n) else "…"
      }

    implicit val intTC: TC[Int] = of[Int](_ => "Int")
    implicit val booleanTC: TC[Boolean] = of[Boolean](_ => "Boolean")
    implicit def optionTC[T: TC]: TC[Option[T]] = of[Option[T]](n => s"Option[${apply[T].msg(n-1)}]")
    implicit def tuple2TC[A: TC, B: TC]: TC[(A, B)] = of[(A, B)](n => s"(${apply[A].msg(n-1)}, ${apply[B].msg(n-1)})")
    implicit val cc1TC: TC[CC1] = of[CC1](_ => "CC1")
  }

  trait TC0[T] {
    def msg(n: Int): String
  }

  object TC0 {
    def apply[T](implicit tc: TC0[T]): TC0[T] = tc

    def of[T](msg0: Int => String): TC0[T] =
      new TC0[T] {
        def msg(n: Int) = if (n >= 0) msg0(n) else "…"
      }

    implicit def defaultTC[T]: TC0[T] = of(_ => "default")

    // These implicits are similar to the ones in the companion of TC above -
    // I found no way to share their definitions (in a common trait like Companion[TC[_]], say)
    // without running into implicit collisions with defaultTC.

    implicit val intTC: TC0[Int] = of[Int](_ => "Int")
    implicit val booleanTC: TC0[Boolean] = of[Boolean](_ => "Boolean")
    implicit def optionTC[T: TC0]: TC0[Option[T]] = of[Option[T]](n => s"Option[${apply[T].msg(n-1)}]")
    implicit def tuple2TC[A: TC0, B: TC0]: TC0[(A, B)] = of[(A, B)](n => s"(${apply[A].msg(n-1)}, ${apply[B].msg(n-1)})")
    implicit val cc1TC: TC0[CC1] = of[CC1](_ => "CC1")
  }
}

trait SimpleDeriver[TC[_] <: {def msg(n: Int): String}] {
  def of[T](msg0: Int => String): TC[T]

  trait MkTC[T] {
    def tc: TC[T]
  }

  object MkTC {
    implicit def hnilMkTC: MkTC[HNil] =
      new MkTC[HNil] {
        val tc = of[HNil](_ => "HNil")
      }
    implicit def hconsMkTC[H, T <: HList]
     (implicit
       head: Strict[TC[H]],
       tail: Strict[MkTC[T]]
     ): MkTC[H :: T] =
      new MkTC[H :: T] {
        lazy val tc = of[H :: T](n => s"${head.value.msg(n-1)} :: ${tail.value.tc.msg(n-1)}")
      }
    implicit def cnilMkTC: MkTC[CNil] =
      new MkTC[CNil] {
        val tc = of[CNil](_ => "CNil")
      }
    implicit def cconsMkTC[H, T <: Coproduct]
     (implicit
       head: Strict[TC[H]],
       tail: Strict[MkTC[T]]
     ): MkTC[H :+: T] =
      new MkTC[H :+: T] {
        lazy val tc = of[H :+: T](n => s"${head.value.msg(n-1)} :+: ${tail.value.tc.msg(n-1)}")
      }
    implicit def genericMkTC[F, G]
     (implicit
       gen: Strict[Generic.Aux[F, G]],
       underlying: Lazy[MkTC[G]]
     ): MkTC[F] =
      new MkTC[F] {
        lazy val tc = of[F](n => s"Generic[${underlying.value.tc.msg(n-1)}]")
      }
  }
}

trait ComposedDeriver[TC[_] <: {def msg(n: Int): String}] {
  def of[T](msg0: Int => String): TC[T]

  trait MkTC[T] {
    def tc: TC[T]
  }

  trait MkStdTC[T] extends MkTC[T]

  object MkStdTC {
    implicit val doubleTC: MkStdTC[Double] =
      new MkStdTC[Double] {
        val tc = of[Double](_ => "Double")
      }

    implicit def mkCollWriter[M[_], T]
     (implicit
       underlying: TC[T],
       cbf: CanBuildFrom[Nothing, T, M[T]]
     ): MkStdTC[M[T]] =
      new MkStdTC[M[T]] {
        lazy val tc = of[M[T]](n => s"${cbf().result().toString.stripSuffix("()")}[${underlying.msg(n - 1)}]")
      }
  }

  trait MkTupleTC[T] extends MkTC[T]

  object MkTupleTC {
    implicit def hnilMkTC: MkTupleTC[HNil] =
      new MkTupleTC[HNil] {
        val tc = of[HNil](_ => "")
      }
    implicit def hconsMkTC[H, T <: HList]
     (implicit
       head: Strict[TC[H]],
       tail: Strict[MkTupleTC[T]]
     ): MkTupleTC[H :: T] =
      new MkTupleTC[H :: T] {
        lazy val tc = of[H :: T]{ n =>
          val tailMsg = tail.value.tc.msg(n-1)
          head.value.msg(n-1) + (if (tailMsg.isEmpty) "" else ", " + tailMsg)
        }
      }
    implicit def genericMkTC[F, G]
     (implicit
       ev: IsTuple[F],
       gen: Strict[Generic.Aux[F, G]],
       underlying: Lazy[MkTupleTC[G]]
     ): MkTupleTC[F] =
      new MkTupleTC[F] {
        lazy val tc = of[F](n => s"Tuple[${underlying.value.tc.msg(n-1)}]")
      }
  }

  trait MkDefaultTC[T] extends MkTC[T]

  object MkDefaultTC {
    implicit def hnilMkTC: MkDefaultTC[HNil] =
      new MkDefaultTC[HNil] {
        val tc = of[HNil](_ => "HNil")
      }
    implicit def hconsMkTC[H, T <: HList]
     (implicit
       head: Strict[TC[H]],
       tail: Strict[MkDefaultTC[T]]
     ): MkDefaultTC[H :: T] =
      new MkDefaultTC[H :: T] {
        lazy val tc = of[H :: T](n => s"${head.value.msg(n-1)} :: ${tail.value.tc.msg(n-1)}")
      }
    implicit def cnilMkTC: MkDefaultTC[CNil] =
      new MkDefaultTC[CNil] {
        val tc = of[CNil](_ => "CNil")
      }
    implicit def cconsMkTC[H, T <: Coproduct]
     (implicit
       head: Strict[TC[H]],
       tail: Strict[MkDefaultTC[T]]
     ): MkDefaultTC[H :+: T] =
      new MkDefaultTC[H :+: T] {
        lazy val tc = of[H :+: T](n => s"${head.value.msg(n-1)} :+: ${tail.value.tc.msg(n-1)}")
      }
    implicit def genericMkTC[F, G]
     (implicit
       gen: Strict[Generic.Aux[F, G]],
       underlying: Lazy[MkDefaultTC[G]]
     ): MkDefaultTC[F] =
      new MkDefaultTC[F] {
        lazy val tc = of[F](n => s"Generic[${underlying.value.tc.msg(n-1)}]")
      }
  }

  implicit def mkTC[T]
   (implicit
     priority: Strict[Priority[TC[T], Implicit[MkStdTC[T] :+: MkTupleTC[T] :+: MkDefaultTC[T] :+: CNil]]]
   ): TC[T] =
    priority.value.fold(identity)(_.value.unify.tc)
}


object SimpleTCDeriver extends SimpleDeriver[TC] {
  def of[T](msg0: Int => String) = TC.of(msg0)

  implicit def mkTC[T]
   (implicit
     priority: Strict[Priority[TC[T], MkTC[T]]]
   ): TC[T] =
    priority.value.fold(identity)(_.tc)
}

object ComposedTCDeriver extends ComposedDeriver[TC] {
  def of[T](msg0: Int => String) = TC.of(msg0)
}

object SimpleTC0Deriver extends SimpleDeriver[TC0] {
  def of[T](msg0: Int => String) = TC0.of(msg0)

  implicit def mkTC[T]
   (implicit
     priority: Strict[Priority[Mask[Witness.`"TC0.defaultTC"`.T, TC0[T]], MkTC[T]]]
   ): TC0[T] =
    priority.value.fold(_.value)(_.tc)
}


class PriorityTests {

  def validateTC[T: TC](expected: String, n: Int = Int.MaxValue): Unit = {
    val msg = TC[T].msg(n)
    assert(expected == msg)
  }

  def validateTC0[T: TC0](expected: String, n: Int = Int.MaxValue): Unit = {
    val msg = TC0[T].msg(n)
    assert(expected == msg)
  }

  @Test
  def simple {
    import SimpleTCDeriver._

    // All orphans
    validateTC[Int]("Int")
    validateTC[CC1]("CC1")
    validateTC[Option[Int]]("Option[Int]")
    validateTC[Option[CC1]]("Option[CC1]")
    validateTC[(Int, CC1)]("(Int, CC1)")
    validateTC[(CC1, Int)]("(CC1, Int)")
    validateTC[(CC1, Boolean)]("(CC1, Boolean)")

    Lazy.mkLazy[TC[CC2]]

    // Derived, then orphans
    validateTC[CC2]("Generic[Int :: HNil]")
    validateTC[Either[Int, CC1]]("Generic[Generic[Int :: HNil] :+: Generic[CC1 :: HNil] :+: CNil]")
    // Fails with the current Orphan
    validateTC[(Int, CC1, Boolean)]("Generic[Int :: CC1 :: Boolean :: HNil]")
    validateTC[(Int, CC2, Boolean)]("Generic[Int :: Generic[Int :: HNil] :: Boolean :: HNil]")

    // Orphan, then derived, then orphans
    validateTC[Option[CC2]]("Option[Generic[Int :: HNil]]")
    validateTC[(Int, CC2)]("(Int, Generic[Int :: HNil])")

    // Cycles

    // Derived (but for TC[Int])
    validateTC[Tree0.Leaf.type]("Generic[HNil]")
    validateTC[Tree0]("Generic[Generic[HNil] :+: Generic[Generic[Generic[HNil] :+: Generic[Generic[Generic[…] :+: … :+: …] :: Generic[… :+: …] :: Int :: HNil] :+: CNil] :: Generic[Generic[HNil] :+: Generic[Generic[… :+: …] :: Generic[…] :: … :: …] :+: CNil] :: Int :: HNil] :+: CNil]", 12)

    // Orphan
    validateTC[Tree.Leaf.type]("Leaf")
    // Interleaved derived / orphans
    // Fails with the current Orphan
    validateTC[Tree]("Generic[Leaf :+: Generic[Generic[Leaf :+: Generic[Generic[Leaf :+: … :+: …] :: Generic[… :+: …] :: Int :: HNil] :+: CNil] :: Generic[Leaf :+: Generic[Generic[… :+: …] :: Generic[…] :: … :: …] :+: CNil] :: Int :: HNil] :+: CNil]", 12)
  }

  @Test
  def composed {
    import ComposedTCDeriver._

    // All orphans
    validateTC[Int]("Int")
    validateTC[CC1]("CC1")
    validateTC[Option[Int]]("Option[Int]")
    validateTC[Option[CC1]]("Option[CC1]")
    validateTC[(Int, CC1)]("(Int, CC1)")
    validateTC[(CC1, Int)]("(CC1, Int)")
    validateTC[(CC1, Boolean)]("(CC1, Boolean)")

    // Derived, then orphans
    validateTC[CC2]("Generic[Int :: HNil]")
    validateTC[CC3]("Generic[Int :: Int :: HNil]")
    validateTC[CC4]("Generic[Double :: HNil]")
    validateTC[CC5]("Generic[List[Double] :: HNil]")
    validateTC[CC6]("Generic[Double :: List[Double] :: HNil]")
    validateTC[Either[Int, CC1]]("Generic[Generic[Int :: HNil] :+: Generic[CC1 :: HNil] :+: CNil]")
    // Fails with the current Orphan
    validateTC[(Int, CC1, Boolean)]("Tuple[Int, CC1, Boolean]")
    validateTC[(Int, CC2, Boolean)]("Tuple[Int, Generic[Int :: HNil], Boolean]")

    // Orphan, then derived, then orphans
    validateTC[Option[CC2]]("Option[Generic[Int :: HNil]]")
    validateTC[(Int, CC2)]("(Int, Generic[Int :: HNil])")

    // Cycles

    // Derived (but for TC[Int])
    validateTC[Tree0.Leaf.type]("Generic[HNil]")
    validateTC[Tree0]("Generic[Generic[HNil] :+: Generic[Generic[Generic[HNil] :+: Generic[Generic[Generic[…] :+: … :+: …] :: Generic[… :+: …] :: Int :: HNil] :+: CNil] :: Generic[Generic[HNil] :+: Generic[Generic[… :+: …] :: Generic[…] :: … :: …] :+: CNil] :: Int :: HNil] :+: CNil]", 12)

    // Orphan
    validateTC[Tree.Leaf.type]("Leaf")
    // Interleaved derived / orphans
    // Fails with the current Orphan
    validateTC[Tree]("Generic[Leaf :+: Generic[Generic[Leaf :+: Generic[Generic[Leaf :+: … :+: …] :: Generic[… :+: …] :: Int :: HNil] :+: CNil] :: Generic[Leaf :+: Generic[Generic[… :+: …] :: Generic[…] :: … :: …] :+: CNil] :: Int :: HNil] :+: CNil]", 12)
  }

  @Test
  def simple0 {
    import SimpleTC0Deriver._

    // More or less cut-n-pasted from 'simple above, I don't really see they could be factored
    // (because of the numerous the implicit lookups)

    // All orphans
    validateTC0[Int]("Int")
    validateTC0[CC1]("CC1")
    validateTC0[Option[Int]]("Option[Int]")
    validateTC0[Option[CC1]]("Option[CC1]")
    validateTC0[(Int, CC1)]("(Int, CC1)")
    validateTC0[(CC1, Int)]("(CC1, Int)")
    validateTC0[(CC1, Boolean)]("(CC1, Boolean)")

    // Derived, then orphans
    validateTC0[CC2]("Generic[Int :: HNil]")
    validateTC0[CC3]("Generic[Int :: Int :: HNil]")
    validateTC0[CC4]("Generic[default :: HNil]")
    validateTC0[CC5]("Generic[Generic[Generic[default :: Generic[Generic[default :: Generic[…] :: HNil] :+: Generic[HNil] :+: CNil] :: HNil] :+: Generic[HNil] :+: CNil] :: HNil]", 12)
    validateTC0[CC6]("Generic[default :: Generic[Generic[default :: Generic[Generic[default :: … :: …] :+: Generic[HNil] :+: CNil] :: HNil] :+: Generic[HNil] :+: CNil] :: HNil]", 12)
    validateTC0[Either[Int, CC1]]("Generic[Generic[Int :: HNil] :+: Generic[CC1 :: HNil] :+: CNil]")
    // Fails with the current Orphan
    validateTC0[(Int, CC1, Boolean)]("Generic[Int :: CC1 :: Boolean :: HNil]")
    validateTC0[(Int, CC2, Boolean)]("Generic[Int :: Generic[Int :: HNil] :: Boolean :: HNil]")

    // Orphan, then derived, then orphans
    validateTC0[Option[CC2]]("Option[Generic[Int :: HNil]]")
    validateTC0[(Int, CC2)]("(Int, Generic[Int :: HNil])")

    // Cycles

    // Derived (but for TC[Int])
    validateTC0[Tree0.Leaf.type]("Generic[HNil]")
    validateTC0[Tree0]("Generic[Generic[HNil] :+: Generic[Generic[Generic[HNil] :+: Generic[Generic[Generic[…] :+: … :+: …] :: Generic[… :+: …] :: Int :: HNil] :+: CNil] :: Generic[Generic[HNil] :+: Generic[Generic[… :+: …] :: Generic[…] :: … :: …] :+: CNil] :: Int :: HNil] :+: CNil]", 12)

    // Orphan
    validateTC0[Tree.Leaf.type]("Leaf")
    // Interleaved derived / orphans
    // Fails with the current Orphan
    validateTC0[Tree]("Generic[Leaf :+: Generic[Generic[Leaf :+: Generic[Generic[Leaf :+: … :+: …] :: Generic[… :+: …] :: Int :: HNil] :+: CNil] :: Generic[Leaf :+: Generic[Generic[… :+: …] :: Generic[…] :: … :: …] :+: CNil] :: Int :: HNil] :+: CNil]", 12)
  }

}
