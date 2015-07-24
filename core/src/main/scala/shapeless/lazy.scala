/*
 * Copyright (c) 2013-15 Miles Sabin
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless

import scala.language.experimental.macros

import scala.collection.immutable.ListMap
import scala.reflect.macros.whitebox

trait Lazy[+T] extends Serializable {
  val value: T

  def map[U](f: T => U): Lazy[U] = Lazy { f(value) }
  def flatMap[U](f: T => Lazy[U]): Lazy[U] = Lazy { f(value).value }
}

object Lazy {
  implicit def apply[T](t: => T): Lazy[T] =
    new Lazy[T] {
      lazy val value = t
    }

  def unapply[T](lt: Lazy[T]): Option[T] = Some(lt.value)

  class Values[T <: HList](val values: T) extends Serializable
  object Values {
    implicit val hnilValues: Values[HNil] = new Values(HNil)
    implicit def hconsValues[H, T <: HList](implicit lh: Lazy[H], t: Values[T]): Values[H :: T] =
      new Values(lh.value :: t.values)
  }

  def values[T <: HList](implicit lv: Lazy[Values[T]]): T = lv.value.values

  implicit def mkLazy[I]: Lazy[I] = macro LazyMacros.mkLazyImpl[I]
}

object lazily {
  def apply[T](implicit lv: Lazy[T]): T = lv.value
}

class LazyMacros(val c: whitebox.Context) {
  import c.universe._
  import c.ImplicitCandidate

  def mkLazyImpl[I](implicit iTag: WeakTypeTag[I]): Tree = {
    (c.openImplicits.headOption, iTag.tpe.dealias) match {
      case (Some(ImplicitCandidate(_, _, TypeRef(_, _, List(tpe)), _)), _) =>
        LazyMacros.deriveInstance(c)(tpe.map(_.dealias))
      case (None, tpe) if tpe.typeSymbol.isParameter =>       // Workaround for presentation compiler
        q"null.asInstanceOf[_root_.shapeless.Lazy[Nothing]]"
      case (None, tpe) =>                                     // Non-implicit invocation
        LazyMacros.deriveInstance(c)(tpe)
      case _ =>
        c.abort(c.enclosingPosition, s"Bad Lazy materialization ${c.openImplicits.head}")
    }
  }
}

object LazyMacros {
  var dcRef: Option[DerivationContext] = None

  def deriveInstance(c: whitebox.Context)(tpe: c.Type): c.Tree = {
    val (dc, root) =
      dcRef match {
        case None =>
          val dc = DerivationContext(c)
          dcRef = Some(dc)
          (dc, true)
        case Some(dc) =>
          (DerivationContext.establish(dc, c), false)
      }

    try {
      dc.State.deriveInstance(tpe, root)
    } finally {
      if(root) dcRef = None
    }
  }
}

object DerivationContext {
  type Aux[C0] = DerivationContext { type C = C0 }

  def apply(c0: whitebox.Context): Aux[c0.type] =
    new DerivationContext {
      type C = c0.type
      val c: C = c0
    }

  def establish(dc: DerivationContext, c0: whitebox.Context): Aux[c0.type] =
    dc.asInstanceOf[DerivationContext { type C = c0.type }]
}

trait LazyExtension {
  type Ctx <: DerivationContext
  val ctx: Ctx

  import ctx._
  import c.universe._

  def id: String

  type ThisState

  def initialState: ThisState

  def derive(
    state0: State,
    extState: ThisState,
    update: (State, ThisState) => State )(
    instTpe0: Type
  ): Option[Either[String, (State, Instance)]]
}

trait LazyExtensionCompanion {
  def instantiate(ctx0: DerivationContext): LazyExtension { type Ctx = ctx0.type }

  def initImpl(c: whitebox.Context): c.universe.Tree = {
    val ctx = LazyMacros.dcRef.getOrElse(
      c.abort(c.enclosingPosition, "")
    )

    val extension = instantiate(ctx)
    ctx.State.addExtension(extension)

    c.abort(c.enclosingPosition, s"Added extension ${extension.id}")
  }
}

trait LazyDefinitions {
  type C <: whitebox.Context
  val c: C

  import c.universe._

  case class Instance(
    instTpe: Type,
    name: TermName,
    symbol: Symbol,
    inst: Option[Tree],
    actualTpe: Type
  ) {
    def ident = Ident(symbol)
  }

  object Instance {
    def apply(instTpe: Type) = {
      val nme = TermName(c.freshName("inst"))
      val sym = c.internal.setInfo(c.internal.newTermSymbol(NoSymbol, nme), instTpe)

      new Instance(instTpe, nme, sym, None, instTpe)
    }
  }

  class TypeWrapper(val tpe: Type) {
    override def equals(other: Any): Boolean =
      other match {
        case TypeWrapper(tpe0) => tpe =:= tpe0
        case _ => false
      }
    override def toString = tpe.toString
  }

  object TypeWrapper {
    def apply(tpe: Type) = new TypeWrapper(tpe)
    def unapply(tw: TypeWrapper): Option[Type] = Some(tw.tpe)
  }


  case class ExtensionWithState[S <: DerivationContext, T](
    extension: LazyExtension { type Ctx = S; type ThisState = T },
    state: T
  ) {
    import extension.ctx

    def derive(
      state0: ctx.State,
      update: (ctx.State, ExtensionWithState[S, T]) => ctx.State )(
      instTpe0: ctx.c.Type
    ): Option[Either[String, (ctx.State, ctx.Instance)]] =
      extension.derive(state0, state, (ctx, t) => update(ctx, copy(state = t)))(instTpe0)
  }

  object ExtensionWithState {
    def apply(extension: LazyExtension): ExtensionWithState[extension.Ctx, extension.ThisState] =
      ExtensionWithState(extension, extension.initialState)
  }

}

trait DerivationContext extends shapeless.CaseClassMacros with LazyDefinitions { ctx =>
  type C <: whitebox.Context
  val c: C

  import c.universe._

  object State {
    final val ctx0: ctx.type = ctx
    val empty = State("", ListMap.empty, Nil)

    private var current = Option.empty[State]
    private var addExtensions = List.empty[ExtensionWithState[ctx.type, _]]

    def addExtension(extension: LazyExtension { type Ctx = ctx0.type }): Unit = {
      addExtensions = ExtensionWithState(extension) :: addExtensions
    }

    def takeNewExtensions(): List[ExtensionWithState[ctx.type, _]] = {
      val addExtensions0 = addExtensions
      addExtensions = Nil
      addExtensions0
    }

    def resolveInstance(state: State)(tpe: Type): Option[(State, Tree)] = {
      val former = State.current
      State.current = Some(state)
      val (state0, tree) =
        try {
          val tree = c.inferImplicitValue(tpe, silent = true)
          (State.current.get, tree)
        } finally {
          State.current = former
        }

      if (tree == EmptyTree || addExtensions.nonEmpty) None
      else Some((state0, tree))
    }

    def deriveInstance(instTpe0: Type, root: Boolean): Tree = {
      if (root) {
        assert(current.isEmpty)
        val open = c.openImplicits
        val name = if (open.length > 1) open(1).sym.name.toTermName.toString else "lazy"
        current = Some(empty.copy(name = name))
      }

      ctx.derive(current.get)(instTpe0) match {
        case Right((state, inst)) =>
          val (tree, actualType) = if (root) mkInstances(state)(instTpe0) else (inst.ident, inst.actualTpe)
          current = if (root) None else Some(state)
          q"_root_.shapeless.Lazy.apply[$actualType]($tree)"
        case Left(err) =>
          abort(err)
      }
    }
  }

  case class State(
    name: String,
    dict: ListMap[TypeWrapper, Instance],
    extensions: List[ExtensionWithState[ctx.type, _]]
  ) {
    def addInstance(d: Instance): State =
      copy(dict = dict.updated(TypeWrapper(d.instTpe), d))

    def lookup(instTpe: Type): Either[State, (State, Instance)] =
      dict.get(TypeWrapper(instTpe))
        .map((this, _))
        .toRight(addInstance(Instance(instTpe)))
  }

  def stripRefinements(tpe: Type): Option[Type] =
    tpe match {
      case RefinedType(parents, decls) => Some(parents.head)
      case _ => None
    }

  def resolve(state0: State)(inst: Instance): Option[(State, Instance)] =
    resolve0(state0)(inst.instTpe)
      .filter{case (_, tree, _) => !tree.equalsStructure(inst.ident) }
      .map {case (state1, extInst, actualTpe) =>
        setTree(state1)(inst.instTpe, extInst, actualTpe)
      }

  def resolve0(state0: State)(instTpe: Type): Option[(State, Tree, Type)] = {
    val extInstOpt =
      State.resolveInstance(state0)(instTpe)
        .orElse(
          stripRefinements(instTpe).flatMap(State.resolveInstance(state0))
        )

    extInstOpt.map {case (state1, extInst) =>
      (state1, extInst, extInst.tpe.finalResultType)
    }
  }

  def setTree(state: State)(tpe: Type, tree: Tree, actualTpe: Type): (State, Instance) = {
    val instance = state.dict(TypeWrapper(tpe))
    val sym = c.internal.setInfo(instance.symbol, actualTpe)
    val instance0 = instance.copy(inst = Some(tree), actualTpe = actualTpe, symbol = sym)
    (state.addInstance(instance0), instance0)
  }

  def derive(state0: State)(instTpe0: Type): Either[String, (State, Instance)] = {
    val fromExtensions: Option[Either[String, (State, Instance)]] =
      state0.extensions.zipWithIndex.foldRight(Option.empty[Either[String, (State, Instance)]]) {
        case (_, acc @ Some(_)) => acc
        case ((ext, idx), None) =>
          def update(state: State, withState: ExtensionWithState[ctx.type, _]) =
            state.copy(extensions = state.extensions.updated(idx, withState))

          ext.derive(state0, update)(instTpe0)
      }

    val result: Either[String, (State, Instance)] =
      fromExtensions.getOrElse {
        state0.lookup(instTpe0).left.flatMap { state =>
          val inst = Instance(instTpe0)
          resolve(state.addInstance(inst))(inst)
            .toRight(s"Unable to derive $instTpe0")
        }
      }

    // Check for newly added extensions, and re-derive with them.
    lazy val current = state0.extensions.map(_.extension.id).toSet
    val newExtensions0 = State.takeNewExtensions().filter(ext => !current(ext.extension.id))
    if (newExtensions0.nonEmpty)
      derive(state0.copy(extensions = newExtensions0 ::: state0.extensions))(instTpe0)
    else
      result
  }

  // Workaround for https://issues.scala-lang.org/browse/SI-5465
  class StripUnApplyNodes extends Transformer {
    val global = c.universe.asInstanceOf[scala.tools.nsc.Global]
    import global.nme

    override def transform(tree: Tree): Tree = {
      super.transform {
        tree match {
          case UnApply(Apply(Select(qual, nme.unapply | nme.unapplySeq), List(Ident(nme.SELECTOR_DUMMY))), args) =>
            Apply(transform(qual), transformTrees(args))
          case t => t
        }
      }
    }
  }

  def mkInstances(state: State)(primaryTpe: Type): (Tree, Type) = {
    val instances = state.dict.values.toList

    val (from, to) = instances.map { d => (d.symbol, NoSymbol) }.unzip

    val instTrees =
      instances.map { instance =>
        import instance._
        inst match {
          case Some(inst) =>
            val cleanInst0 = c.untypecheck(c.internal.substituteSymbols(inst, from, to))
            val cleanInst = new StripUnApplyNodes().transform(cleanInst0)
            q"""lazy val $name: $actualTpe = $cleanInst.asInstanceOf[$actualTpe]"""
          case None =>
            abort(s"Uninitialized $instTpe lazy implicit")
        }
      }

    val primaryInstance = state.dict(TypeWrapper(primaryTpe))
    val primaryNme = primaryInstance.name
    val clsName = TypeName(c.freshName(state.name))

    val tree =
      q"""
        final class $clsName extends _root_.scala.Serializable {
          ..$instTrees
        }
        (new $clsName).$primaryNme
       """
    val actualType = primaryInstance.actualTpe

    (tree, actualType)
  }
}
