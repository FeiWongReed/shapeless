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

  def derive(
    state0: State,
    extState: ThisState,
    update: (State, ThisState) => State )(
    instTpe0: Type
  ): Option[Either[String, (State, Instance)]] =
    instTpe0 match {
      case TraceTpe(tpe) =>
        Some {
          state0.lookup(instTpe0).left.flatMap { state =>
            ctx.derive(state)(tpe).right.map{case (state0, inst0) =>
              val actualType1 = appliedType(traceTpe, List(inst0.actualTpe))
              val (state1, inst) = setTree(state0)(instTpe0, q"_root_.shapeless.Trace.mkTrace[${inst0.actualTpe}](${inst0.ident})", actualType1)
              println(s"$tpe trace:\n${inst0.ident}\n${state1.dict.map{case (k, v) => s"$k\n  $v\n"}.mkString("\n")}")
              (state1, inst)
            }
          }
        }

      case _ => None
    }

}
