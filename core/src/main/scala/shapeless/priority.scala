package shapeless

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Looking for an implicit `Lazy[Priority[H, L]]` will look up for an implicit `H`,
 * or, if it fails, for an implicit `L`, and wrap the result in a `Lazy[Priority[H, L]]`.
 *
 * It allows for definitions like
 *     implicit def mkTC[T]
 *      (implicit
 *        impl: Lazy[Implicit[
 *          TC[T],
 *          Fallback[T]
 *        ]]
 *      ): TC[T] = impl.value.fold(identity)(_.toTC)
 * which is looking for an implicit `TC[T]`, but at the same time providing one. Without `Priority`,
 * this would typically lead to stack overflows at runtime, as `mkTC` would find itself as a `TC[T]`,
 * and call itself without terminating. Thanks to `Priority`, the lookup for a `TC[T]` by `mkTC` will
 * ignore the implicit `TC[T]` it itself provides, hence only looking for `TC[T]` elsewhere. Note that
 * this does not prevent `mkTC` to provide `TC` instances the same way for other types during the search
 * for a `TC[T]` or `Fallback[T]`.
 */
trait Priority[+H, +L] extends Serializable {
  def fold[T](high: H => T)(low: L => T): T =
    this match {
      case Priority.High(h) => high(h)
      case Priority.Low(l) => low(l)
    }
}

object Priority extends LazyExtensionCompanion {
  case class High[+H](value: H) extends Priority[H, Nothing]
  case class Low[+L](value: L) extends Priority[Nothing, L]

  def apply[H, L](implicit lkpPriority: Lazy[Priority[H, L]]): Priority[H, L] =
    lkpPriority.value


  implicit def init[H, L]: Priority[H, L] = macro initImpl

  def instantiate(ctx0: DerivationContext) =
    new PriorityLookupExtension {
      type Ctx = ctx0.type
      val ctx: ctx0.type = ctx0
    }
}

/**
 * Allows to mask some high priority implicits in a `Priority[H, L]` lookup.
 *
 * Typical usage is when a fallback for type class `TC` is defined in its companion, like
 *     object TC {
 *       implicit def anyTC[T]: TC[T] = ...
 *     }
 *
 * If one looks for a `Priority[TC[T], Other[T]]`, then the lookup for a `TC[T]` will always
 * succeed, because of the `anyTC` case above. With `Mask`, one can instead look for
 * a ``Priority[Mask[W.`anyTC`.T, TC[T]], Other[T]]``. This `Priority` will first look up
 * for a `TC[T]`, but will not accept it being made by `anyTC[T]`. Else, it will lookup for
 * a `Other[T]`.
 */
trait Mask[M, T] extends Serializable {
  def value: T
}

object Mask {
  def apply[M, T](implicit lkpMask: Lazy[Mask[M, T]]): Mask[M, T] = lkpMask.value

  def mkMask[M, T](t: T): Mask[M, T] =
    new Mask[M, T] {
      val value = t
    }
}


trait PriorityTypes {
  type C <: whitebox.Context
  val c: C

  import c.universe._


  def highPriorityTpe: Type = typeOf[Priority.High[_]].typeConstructor
  def lowPriorityTpe: Type = typeOf[Priority.Low[_]].typeConstructor
  def priorityTpe: Type = typeOf[Priority[_, _]].typeConstructor

  object PriorityTpe {
    def unapply(tpe: Type): Option[(Type, Type)] =
      tpe.dealias match {
        case TypeRef(_, cpdTpe, List(highTpe, lowTpe))
          if cpdTpe.asType.toType.typeConstructor =:= priorityTpe =>
          Some(highTpe, lowTpe)
        case _ =>
          None
      }
  }

  def maskTpe: Type = typeOf[Mask[_, _]].typeConstructor

  object MaskTpe {
    def unapply(tpe: Type): Option[(Type, Type)] =
      tpe.dealias match {
        case TypeRef(_, cpdTpe, List(mTpe, tTpe))
          if cpdTpe.asType.toType.typeConstructor =:= maskTpe =>
          Some(mTpe, tTpe)
        case _ =>
          None
      }
  }

}

trait PriorityLookupExtension extends LazyExtension with PriorityTypes {
  type C = ctx.c.type
  lazy val c: C = ctx.c

  import ctx._
  import c.universe._

  case class ThisState(
    priorityLookups: List[TypeWrapper]
  ) {
    def addPriorityLookup(tpe: Type*): ThisState =
      copy(priorityLookups = tpe.toList.map(TypeWrapper(_)) ::: priorityLookups)
    def removePriorityLookup(tpe: Type*): ThisState =
      tpe.foldLeft(this)((s, t) => s.copy(priorityLookups = priorityLookups.filter(_ != TypeWrapper(t))))
  }

  def id = "priority"

  def initialState = ThisState(Nil)

  def derivePriority(
    get: LazyState => ThisState,
    update: (LazyState, ThisState) => LazyState )(
    highInstTpe: Type,
    lowInstTpe: Type,
    mask: String
  ): LazyStateT[Option[(Tree, Type)]] = {
    val high0: LazyStateT[Option[(Tree, Type)]] = {
      def open[T](t: T) =
        LazyStateT[T] { state =>
          val l = state.open.map(_.instTpe).takeWhile(tpe => !(tpe =:= highInstTpe))
          val extState1 = get(state)
            .addPriorityLookup(l: _*)
          (update(state, extState1), t)
        }
      def close[T](t: T) =
        LazyStateT[T] { state =>
          val l = state.open.map(_.instTpe).takeWhile(tpe => !(tpe =:= highInstTpe))
          val extState1 = get(state)
            .removePriorityLookup(l: _*)
          (update(state, extState1), t)
        }

      open(())
        .flatMap { _ =>
          ctx.derive(highInstTpe, depIfEmpty = false).map(_.right.toOption)
        }
        .flatMap {
          case None => LazyStateT.point(None)
          case Some(inst) =>
            if (inst.inst.isEmpty)
              resolve0(highInstTpe)
                .map(_.map{case (tree, tpe) => (tree, tree, tpe) })
            else
              LazyStateT.point(Some((inst.ident, inst.inst.get, inst.actualTpe)))
        }
        .map{
          _.filter { case (_, actualTree, _) =>
            mask.isEmpty || {
              actualTree match {
                case TypeApply(method, other) =>
                  !method.toString().endsWith(mask)
                case _ =>
                  true
              }
            }
          }
          .map { case (tree0, _, actualTpe) =>
            if (mask.isEmpty)
              (tree0, actualTpe)
            else {
              val mTpe = internal.constantType(Constant(mask))
              (q"_root_.shapeless.Mask.mkMask[$mTpe, $actualTpe]($tree0)", appliedType(maskTpe, List(mTpe, actualTpe)))
            }
          }
        }
        .flatMap(close)
        .map{
          _.map { case (tree, actualType) =>
            (q"_root_.shapeless.Priority.High[$actualType]($tree)", appliedType(highPriorityTpe, List(actualType)))
          }
        }
    }

    val low0: LazyStateT[Option[(Tree, Type)]] =
      ctx.derive(lowInstTpe).map(_.right.toOption)
        .map{
          _.map { inst =>
            (q"_root_.shapeless.Priority.Low[${inst.actualTpe}](${inst.ident})", appliedType(lowPriorityTpe, List(inst.actualTpe)))
          }
        }

    LazyStateT
      .mix(high0){ (orig, new0, res) =>
        if (res.nonEmpty) new0.copy(noImpl = orig.noImpl)
        else orig
      }
      .flatMap {
        case s @ Some(_) => LazyStateT.point(s)
        case None => low0
      }
  }

  private def matchPriorityTpe(tpe: Type, get: LazyState => ThisState): LazyStateT[Option[Either[String, (Type, Type)]]] =
    LazyStateT { state =>
      if (get(state).priorityLookups.contains(TypeWrapper(tpe)))
        (state, Some(Left(s"Not deriving $tpe")))
      else
        (state, tpe match {
          case PriorityTpe(highTpe, lowTpe) =>
            if (state.lookup(tpe).isEmpty)
              Some(Right((highTpe, lowTpe)))
            else
              None
          case _ =>
            None
        })
    }

  def derive(
    get: LazyState => ThisState,
    update: (LazyState, ThisState) => LazyState )(
    instTpe0: Type
  ): LazyStateT[Option[Either[String, Instance]]] =
    matchPriorityTpe(instTpe0, get)
      .flatMap {
        case None => LazyStateT.point(None)
        case Some(Left(err)) => LazyStateT.point(Some(Left(err)))

        case Some(Right((highTpe0, lowTpe))) =>
          LazyStateT(s => (s, s.lookup(instTpe0)))
            .flatMap {
              case Some(res) => LazyStateT.point(res)
              case None =>
                val eitherHighTpeMask =
                  highTpe0 match {
                    case MaskTpe(mTpe, tTpe) =>
                      mTpe match {
                        case ConstantType(Constant(mask: String)) if mask.nonEmpty =>
                          Right((tTpe, mask))
                        case _ =>
                          Left(s"Unsupported mask type: $mTpe")
                      }
                    case _ =>
                      Right((highTpe0, ""))
                  }

                eitherHighTpeMask match {
                  case Left(err) => LazyStateT.point(Left(err))
                  case Right((highTpe, mask)) =>
                    LazyStateT(_.openInst(instTpe0))
                      .flatMap(_ =>
                        derivePriority(get, update)(highTpe, lowTpe, mask)
                          .flatMap {
                            case None =>
                              LazyStateT(state => (state.failedInst(instTpe0), None))
                            case Some((tree, tpe)) =>
                              LazyStateT(_.closeInst(instTpe0, tree, tpe))
                                .map(Some(_))
                          }
                          .map(_.toRight(s"Unable to derive $instTpe0"))
                      )
                }
            }
            .map(Some(_))
      }

}

