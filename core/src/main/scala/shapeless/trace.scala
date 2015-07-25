package shapeless

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * For debugging purposes. Looking for a `Lazy[Trace[T]]` will print in the console
 * the generated `Lazy[Trace[T]]` instance during compilation, allowing one to inspect
 * the intermediate implicits solved during this lookup.
 */
trait Trace[T] {
  def value: T
}

object Trace extends LazyExtensionCompanion {
  def apply[T](implicit lkpTrace: Lazy[Trace[T]]): Trace[T] = lkpTrace.value

  def mkTrace[T](t: => T): Trace[T] =
    new Trace[T] {
      def value = t
    }


  implicit def init[T]: Trace[T] = macro initImpl

  def instantiate(ctx0: DerivationContext) =
    new TraceLookupExtension {
      type Ctx = ctx0.type
      val ctx: ctx0.type = ctx0
    }
}


trait TraceTypes {
  type C <: whitebox.Context
  val c: C

  import c.universe._


  def traceTpe: Type = typeOf[Trace[_]].typeConstructor

  object TraceTpe {
    def unapply(tpe: Type): Option[Type] =
      tpe.dealias match {
        case TypeRef(_, cpdTpe, List(tTpe))
          if cpdTpe.asType.toType.typeConstructor =:= traceTpe =>
          Some(tTpe)
        case _ =>
          None
      }
  }

}

trait TraceLookupExtension extends LazyExtension with TraceTypes {
  type C = ctx.c.type
  lazy val c: C = ctx.c

  import ctx._
  import c.universe._

  case object ThisState
  type ThisState = ThisState.type

  def id = "trace"

  def initialState = ThisState

  private def matchTraceTpe(tpe: Type): LazyStateT[Option[Type]] =
    LazyStateT { state =>
      (state, tpe match {
        case TraceTpe(tTpe) if !state.dict.contains(TypeWrapper(tpe)) => Some(tTpe)
        case _ => None
      })
    }

  def derive(
    get: LazyState => ThisState,
    update: (LazyState, ThisState) => LazyState )(
    instTpe0: Type
  ): LazyStateT[Option[Either[String, Instance]]] =
    matchTraceTpe(instTpe0)
      .flatMap {
        case None => LazyStateT.point(None)
        case Some(tpe) =>
          LazyStateT(_.openInst(instTpe0))
            .flatMap(_ => ctx.derive(tpe))
            .flatMap{
              case l @ Left(_) =>
                LazyStateT(state => (state.failedInst(instTpe0), l))
              case Right(inst0) =>
                val actualType = appliedType(traceTpe, List(inst0.actualTpe))
                val tree = q"_root_.shapeless.Trace.mkTrace[${inst0.actualTpe}](${inst0.ident})"
                LazyStateT(_.closeInst(instTpe0, tree, actualType))
                  .map(Right(_))
            }
            .map(Some(_))
      }

}
