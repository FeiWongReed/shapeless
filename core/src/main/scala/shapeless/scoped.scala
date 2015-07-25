package shapeless

import scala.collection.immutable.ListMap
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

trait Scoped[S <: String, +T] extends Serializable {
  val value: T
}

object Scoped extends LazyExtensionCompanion {
  def apply[S <: String, T](t: T): Scoped[S, T] =
    new Scoped[S, T] {
      val value = t
    }

  implicit def init[S <: String, T]: Scoped[S, T] = macro initImpl

  def instantiate(ctx0: DerivationContext) =
    new ScopedLookupExtension {
      type Ctx = ctx0.type
      val ctx: ctx0.type = ctx0
    }
}

trait ScopedTypes {
  type C <: whitebox.Context
  val c: C

  import c.universe._


  def scopedTpe: Type = typeOf[Scoped[_, _]].typeConstructor

  object ScopedTpe {
    def unapply(tpe: Type): Option[(String, Type)] =
      tpe.dealias match {
        case TypeRef(_, cpdTpe, List(ConstantType(Constant(s: String)), tTpe))
          if cpdTpe.asType.toType.typeConstructor =:= scopedTpe =>
          Some((s, tTpe))
        case _ =>
          None
      }
  }

}

object ScopedLookupExtension {
  var cache = Map.empty[String, (Any, Any)]
}

trait ScopedLookupExtension extends LazyExtension with ScopedTypes {
  type C = ctx.c.type
  lazy val c: C = ctx.c

  import ctx._
  import c.universe._

  case class ThisState(
    current: String
  )

  def id = "scoped"

  def initialState = ThisState("")

  private def matchScopedTpe(tpe: Type): LazyStateT[Option[(String, Type)]] =
    LazyStateT { state =>
      (state, tpe match {
        case ScopedTpe(scope, tTpe) if !state.dict.contains(TypeWrapper(tpe)) => Some((scope, tTpe))
        case _ => None
      })
    }

  private def setupScope[T](
    scope: String,
    get: LazyState => ThisState,
    update: (LazyState, ThisState) => LazyState )(
    t: T
  ): LazyStateT[T] =
    LazyStateT { state =>
      val extState = get(state)

      if (extState.current.nonEmpty && extState.current != scope)
        abort(s"Conflicting scopes (${extState.current}, $scope)")
      else {
        val state0 =
          if (extState.current.isEmpty) {
            if (state.dict.exists(_._2.inst.nonEmpty))
              abort(s"Scoped from non root lookup ($scope)")
            else {
              val (dictFromCache, noImplFromCache) =
                ScopedLookupExtension.cache.get(scope) match {
                  case Some((dict0, failed0)) =>
                    (dict0.asInstanceOf[ListMap[TypeWrapper, Instance]], failed0.asInstanceOf[List[TypeWrapper]])
                  case None =>
                    ScopedLookupExtension.cache += scope -> ((state.dict, state.noImpl))
                    (state.dict, state.noImpl)
                }

              update(state.copy(dict = dictFromCache, noImpl = noImplFromCache), ThisState(scope))
            }
          } else
            state

        (state0, t)
      }
    }

  def keepCache[T](scope: String)(t: T): LazyStateT[T] =
    LazyStateT { state =>
      ScopedLookupExtension.cache += scope -> ((state.dict, state.noImpl))
      (state, t)
    }

  def derive(
    get: LazyState => ThisState,
    update: (LazyState, ThisState) => LazyState )(
    instTpe0: Type
  ): LazyStateT[Option[Either[String, Instance]]] =
    matchScopedTpe(instTpe0)
      .flatMap {
        case None => LazyStateT.point(None)
        case Some((scope, tpe)) =>
          setupScope(scope, get, update)(())
            .flatMap { _ =>
              def derive =
                LazyStateT(_.openInst(instTpe0))
                  .flatMap(_ => ctx.derive(tpe))
                  .flatMap {
                    case l @ Left(_) =>
                      LazyStateT(state => (state.failedInst(instTpe0), l))
                    case Right(inst0) =>
                      val sTpe = internal.constantType(Constant(scope))
                      val tree = q"_root_.shapeless.Scoped.apply[$sTpe, ${inst0.actualTpe}](${inst0.ident})"
                      val actualType = appliedType(scopedTpe, List(sTpe, inst0.actualTpe))
                      LazyStateT(_.closeInst(instTpe0, tree, actualType))
                        .map(Right(_))
                  }

              LazyStateT(state => (state, state.lookup(instTpe0)))
                .flatMap {
                  case Some(inst) => LazyStateT.point(Right(inst))
                  case None => derive
                }
            }
            .flatMap(keepCache(scope))
            .map(Some(_))
      }

}
