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

trait Strict[+T] extends Serializable {
  val value: T

  def map[U](f: T => U): Strict[U] = Strict { f(value) }
  def flatMap[U](f: T => Strict[U]): Strict[U] = Strict { f(value).value }
}

object Strict {
  implicit def apply[T](t: T): Strict[T] =
    new Strict[T] {
      val value = t
    }

  def unapply[T](lt: Strict[T]): Option[T] = Some(lt.value)

  implicit def mkStrict[I]: Strict[I] = macro LazyMacros.mkStrictImpl[I]
}

class LazyMacros(val c: whitebox.Context) {
  import c.universe._
  import c.ImplicitCandidate

  def mkLazyImpl[I](implicit iTag: WeakTypeTag[I]): Tree =
    mkImpl[I](strict = false)

  def mkStrictImpl[I](implicit iTag: WeakTypeTag[I]): Tree =
    mkImpl[I](strict = true)

  def mkImpl[I](strict: Boolean)(implicit iTag: WeakTypeTag[I]): Tree = {
    (c.openImplicits.headOption, iTag.tpe.dealias) match {
      case (Some(ImplicitCandidate(_, _, TypeRef(_, _, List(tpe)), _)), _) =>
        LazyMacros.deriveInstance(c)(tpe.map(_.dealias), strict)
      case (None, tpe) if tpe.typeSymbol.isParameter =>       // Workaround for presentation compiler
        q"null.asInstanceOf[_root_.shapeless.Lazy[Nothing]]"
      case (None, tpe) =>                                     // Non-implicit invocation
        LazyMacros.deriveInstance(c)(tpe, strict)
      case _ =>
        c.abort(c.enclosingPosition, s"Bad Lazy materialization ${c.openImplicits.head}")
    }
  }
}

object LazyMacros {
  var dcRef: Option[DerivationContext] = None

  var startTime = 0L
  var count = 0
  var verbose = true

  var cacheMiss = Set.empty[String]

  def deriveInstance(c: whitebox.Context)(tpe: c.Type, strict: Boolean): c.Tree = {
    val (dc, root) =
      dcRef match {
        case None =>
          val dc = DerivationContext(c)
          dcRef = Some(dc)
          (dc, true)
        case Some(dc) =>
          (DerivationContext.establish(dc, c), false)
      }

    if (verbose && root) {
      if (startTime == 0L)
        startTime = System.currentTimeMillis()
      count += 1
      println(s"Deriving $tpe ${((if (strict) Seq("strict") else Seq()) ++ Seq(count.toString, ((System.currentTimeMillis() - startTime) / 1000.0).toString)).mkString("(", ", ", ")")}")
    }

    if (root)
      // Sometimes corrupted
      c.universe.asInstanceOf[scala.tools.nsc.Global].analyzer.resetImplicits()

    try {
      val result = dc.LazyState.deriveInstance(tpe, root, strict)
      if (verbose && root)
        println(s"-> Derived $tpe" + (if (strict) " (strict)" else ""))
      result
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
    get: LazyState => ThisState,
    update: (LazyState, ThisState) => LazyState )(
    instTpe0: Type
  ): LazyStateT[Option[Either[String, Instance]]]
}

trait LazyExtensionCompanion {
  def instantiate(ctx0: DerivationContext): LazyExtension { type Ctx = ctx0.type }

  def initImpl(c: whitebox.Context): c.universe.Tree = {
    val ctx = LazyMacros.dcRef.getOrElse(
      c.abort(c.enclosingPosition, "")
    )

    val extension = instantiate(ctx)
    ctx.LazyState.addExtension(extension)

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
    actualTpe: Type,
    dependsOn: List[Type]
  ) {
    def ident = Ident(symbol)
  }

  object Instance {
    def apply(instTpe: Type) = {
      val nme = TermName(c.freshName("inst"))
      val sym = c.internal.setInfo(c.internal.newTermSymbol(NoSymbol, nme), instTpe)

      new Instance(instTpe, nme, sym, None, instTpe, Nil)
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
      get: ctx.LazyState => ExtensionWithState[S, _], // FIXME Should be T instead of _
      update: (ctx.LazyState, ExtensionWithState[S, T]) => ctx.LazyState )(
      instTpe0: ctx.c.Type
    ): ctx.LazyStateT[Option[Either[String, ctx.Instance]]] =
      extension.derive(get(_).state.asInstanceOf[T], (ctx, t) => update(ctx, copy(state = t)))(instTpe0)
  }

  object ExtensionWithState {
    def apply(extension: LazyExtension): ExtensionWithState[extension.Ctx, extension.ThisState] =
      ExtensionWithState(extension, extension.initialState)
  }

}

object State {
  class Builder[S] {
    def apply[A](a: A): State[S, A] = State[S, A]((_, a))
  }
  def point[S]: Builder[S] = new Builder[S]

  def withRollback[S, A](s: State[S, A])(pred: A => Boolean): State[S, A] =
    State { s0 =>
      val (s1, a) = s.run(s0)
      if (pred(a))
        (s1, a)
      else
        (s0, a)
    }
  def mix[S, A](s: State[S, A])(f: (S, S, A) => S): State[S, A] =
    State { s0 =>
      val (s1, a) = s.run(s0)
      (f(s0, s1, a), a)
    }
}

case class State[S, +A](run: S => (S, A)) {
  def map[B](f: A => B): State[S, B] =
    State { s0 =>
      val (s, a) = run(s0)
      (s, f(a))
    }
  def flatMap[B](f: A => State[S, B]): State[S, B] =
    State { s0 =>
      val (s, a) = run(s0)
      f(a).run(s)
    }
}

trait DerivationContext extends shapeless.CaseClassMacros with LazyDefinitions { ctx =>
  type C <: whitebox.Context
  val c: C

  import c.universe._

  object LazyState {
    final val ctx0: ctx.type = ctx
    val empty = LazyState("", ListMap.empty, Nil, Nil, Nil)

    private var current = Option.empty[LazyState]
    private var addExtensions = List.empty[ExtensionWithState[ctx.type, _]]

    def addExtension(extension: LazyExtension { type Ctx = ctx0.type }): Unit = {
      addExtensions = ExtensionWithState(extension) :: addExtensions
    }

    def takeNewExtensions(): List[ExtensionWithState[ctx.type, _]] = {
      val addExtensions0 = addExtensions
      addExtensions = Nil
      addExtensions0
    }

    def resolveInstance(tpe: Type) =
      LazyStateT[Option[Tree]] { state =>
        val former = LazyState.current
        LazyState.current = Some(state)
        val (state0, tree) =
          try {
//            if (LazyMacros.verbose) {
//              val s = tpe.toString
//              if (LazyMacros.cacheMiss(s))
//                println(s"\n    Cache miss:\n  $s\n" + state.dict.get(TypeWrapper(tpe)).filter(_.inst.nonEmpty).fold("")(inst => s"    Was in cache\n${Thread.currentThread.getStackTrace.map(_.toString).takeWhile(!_.startsWith("scala.tools.nsc.")).map("    " + _).mkString("\n")}"))
//              else
//                LazyMacros.cacheMiss += s
//            }
            val tree = c.inferImplicitValue(tpe, silent = true)
//            if (LazyMacros.verbose) {
//              if (tree == EmptyTree)
//                println(s"Failed implicit ($tpe)")
//            }
            (LazyState.current.get, tree)
          } finally {
            LazyState.current = former
          }

        (
          state0,
          if (tree == EmptyTree || addExtensions.nonEmpty) None
          else Some(tree)
        )
      }

    def deriveInstance(instTpe0: Type, root: Boolean, strict: Boolean): Tree = {
      if (root) {
        assert(current.isEmpty)
        val open = c.openImplicits
        val name = if (open.length > 1) open(1).sym.name.toTermName.toString else if (strict) "strict" else "lazy"
        current = Some(empty.copy(name = name))
      }

      val (state, eitherInst) = ctx.derive(instTpe0).run(current.get)
      current = if (root) None else Some(state)
      eitherInst match {
        case Right(inst) =>
          //if (!root)
            //current = current
          val (tree, actualType) = if (root) mkInstances(state)(instTpe0) else (inst.ident, inst.actualTpe)
          if (strict) q"_root_.shapeless.Strict.apply[$actualType]($tree)"
          else q"_root_.shapeless.Lazy.apply[$actualType]($tree)"
        case Left(err) =>
//          if (LazyMacros.verbose)
//            println(s"Error $instTpe0: $err")
          abort(err)
      }
    }
  }

  case class LazyState(
    name: String,
    dict: ListMap[TypeWrapper, Instance],
    noImpl: List[TypeWrapper],
    open: List[Instance],
    extensions: List[ExtensionWithState[ctx.type, _]]
  ) {
    def addDependency(tpe: Type): LazyState = {
      import scala.::
      val open0 = open match {
        case Nil => Nil
        case h :: t => h.copy(dependsOn = if (h.instTpe =:= tpe || h.dependsOn.exists(_ =:= tpe)) h.dependsOn else tpe :: h.dependsOn) :: t
      }
      copy(open = open0)
    }
    private def update(inst: Instance): LazyState =
      copy(dict = dict.updated(TypeWrapper(inst.instTpe), inst))
    private def remove(tpe: Type): LazyState =
      copy(dict = dict - TypeWrapper(tpe))
    def openInst(tpe: Type): (LazyState, Instance) = {
      val inst = Instance(tpe)
      val state0 = addDependency(tpe)
      (state0.copy(open = inst :: state0.open).update(inst), inst)
    }

    def closeInst(tpe: Type, tree: Tree, actualTpe: Type): (LazyState, Instance) = {
      assert(open.nonEmpty)
      assert(open.head.instTpe =:= tpe)
//      if (LazyMacros.verbose)
//        println(s"Closing $tpe with\n  $tree")
      val instance = open.head
      val sym = c.internal.setInfo(instance.symbol, actualTpe)
      val instance0 = instance.copy(inst = Some(tree), actualTpe = actualTpe, symbol = sym)
      (copy(open = open.tail).update(instance0), instance0)
    }

    def failedInst(tpe: Type): LazyState = {
      assert(open.nonEmpty)
      assert(open.head.instTpe =:= tpe)

      val dependsOn0 = dependsOn(tpe)

      import scala.::
      val open0 = open.tail match {
        case Nil => Nil
        case h :: t => h.copy(dependsOn = h.dependsOn.filterNot(_ =:= tpe)) :: t
      }

//      if (LazyMacros.verbose)
//        println(s"Failed: $tpe\n")

      val s = tpe.toString
      (copy(
        open = open0,
        dict = dict,
        noImpl = TypeWrapper(tpe) :: noImpl
      ) /: dependsOn0)(_ remove _.instTpe)
    }

    def lookup(instTpe: Type): Option[Either[String, Instance]] =
      dict.get(TypeWrapper(instTpe)).map(Right(_))
        .orElse(
          if (noImpl.contains(TypeWrapper(instTpe)))
            Some(Left(s"No implicit available for $instTpe"))
          else
            None
        )

    def dependsOn(tpe: Type): List[Instance] = {
      import scala.::
      def helper(tpes: List[List[Type]], acc: List[Instance]): List[Instance] =
        tpes match {
          case Nil => acc
          case Nil :: t =>
            helper(t, acc)
          case (h :: t0) :: t =>
            if (acc.exists(_.instTpe =:= h))
              helper(t0 :: t, acc)
            else {
              val inst = dict(TypeWrapper(h))
              helper(inst.dependsOn :: t0 :: t, inst :: acc)
            }
        }

      helper(List(List(tpe)), Nil)
    }
  }

  type LazyStateT[+A] = State[LazyState, A]
  object LazyStateT {
    def point[A](a: A): LazyStateT[A] = State.point[LazyState](a)
    def apply[A](f: LazyState => (LazyState, A)): LazyStateT[A] =
      State[LazyState, A](f)
    def withRollback[A](s: LazyStateT[A])(pred: A => Boolean): LazyStateT[A] =
      State.withRollback[LazyState, A](s)(pred)
    def mix[A](s: LazyStateT[A])(f: (LazyState, LazyState, A) => LazyState): LazyStateT[A] =
      State.mix[LazyState, A](s)(f)
  }

  def stripRefinements(tpe: Type): Option[Type] =
    tpe match {
      case RefinedType(parents, decls) => Some(parents.head)
      case _ => None
    }

  def resolve(inst: Instance): LazyStateT[Option[Instance]] =
    resolve0(inst.instTpe)
      .map{
        _.filter { case (tree, _) => !tree.equalsStructure(inst.ident) }
      }
      .flatMap {
        case None =>
          LazyStateT(state => (state.failedInst(inst.instTpe), None))
        case Some((tree, tpe)) =>
          LazyStateT(_.closeInst(inst.instTpe, tree, tpe))
            .map(Some(_))
      }

  def resolve0(instTpe: Type): LazyStateT[Option[(Tree, Type)]] =
    LazyState.resolveInstance(instTpe)
      .flatMap {
        case s @ Some(_) => LazyStateT.point(s)
        case None =>
          stripRefinements(instTpe) match {
            case None => LazyStateT.point(None)
            case Some(t) => LazyState.resolveInstance(t)
          }
      }
      .map {
        _.map{ extInst => (extInst, extInst.tpe.finalResultType) }
      }

  def derive(instTpe0: Type, depIfEmpty: Boolean = true): LazyStateT[Either[String, Instance]] =
    LazyStateT[Either[String, Instance]] { state =>
      import language.existentials

      val fromExtensions =
        state.extensions.zipWithIndex.foldRight(LazyStateT.point(Option.empty[Either[String, Instance]])) {case ((ext, idx), accT) =>
          def get(state: LazyState): ExtensionWithState[ctx.type, _] =
            state.extensions(idx)
          def update(state: LazyState, withState: ExtensionWithState[ctx.type, _]) =
            state.copy(extensions = state.extensions.updated(idx, withState))

          accT.flatMap {
            case s @ Some(_) => LazyStateT.point(s)
            case None => ext.derive(get, update)(instTpe0)
          }
        }

      val result =
        fromExtensions.flatMap {
          case Some(s) => LazyStateT.point(s)
          case None =>
            val msg = LazyStateT{ s =>
              (s, ())
            }
            msg.flatMap(_ => LazyStateT(s => (s, s.lookup(instTpe0))))
              .flatMap {
                case Some(res) =>
                  LazyStateT { state =>
                    val state0 =
                      res match {
                        case Left(_) =>
                          state
                        case Right(i) =>
                          if (depIfEmpty || i.inst.nonEmpty)
                            state.addDependency(instTpe0)
                          else
                            state
                      }

                    (state0, res)
                  }
                case None =>
                  LazyStateT(_.openInst(instTpe0))
                    .flatMap(resolve)
                    .map(_.toRight(s"Unable to derive $instTpe0"))
              }
        }

      // Check for newly added extensions, and re-derive with them.
      result.flatMap { res =>
        LazyStateT { s =>
          lazy val current = s.extensions.map(_.extension.id).toSet
          val newExtensions0 = LazyState.takeNewExtensions().filter(ext => !current(ext.extension.id))
          if (newExtensions0.nonEmpty)
            derive(instTpe0).run(state.copy(extensions = newExtensions0 ::: s.extensions))
          else
            (s, res)
        }
      } .run(state)
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

  class Inliner(sym: Name, inlined: Tree) extends Transformer {
    var count = 0

    override def transform(tree: Tree): Tree =
      super.transform {
        tree match {
          case Ident(sym0) if sym0 == sym =>
            count += 1
            inlined
          case t => t
        }
      }
  }

  object Instances {
    def canBeInlined(t: (Instance, List[String])): Boolean = {
      val (inst, dependees) = t
      inst.dependsOn.isEmpty && dependees.lengthCompare(1) == 0
    }

    def priorityCanBeSubstituted(t: (Instance, List[String])): Option[Tree] = {
      import scala.::
      val (inst, dependees) = t
      if (inst.dependsOn.nonEmpty)
        None
      else
        inst.inst.get match {
          case q"$method[..$tp](shapeless.Strict.apply[..$tpa](_root_.shapeless.Priority.High[..${(tph: TypeTree) :: Nil}]($something)))"
            // FIXME Is it the right test when actualTpe =!:= instTpe in the high priority lookup?
            if tph.tpe =:= inst.actualTpe => Some(something)
          case other =>
            None
        }
    }

    def apply(state: LazyState, primaryTpe: Type): Instances = {
      val instances = state.dependsOn(primaryTpe)
      var m = Map.empty[String, List[String]]

      for (inst <- instances) {
        val name = inst.name.toString

        for (depTpe <- inst.dependsOn) {
          val depInst = state.dict(TypeWrapper(depTpe))
          val depName = depInst.name.toString
          m += depName -> (name :: m.getOrElse(depName, Nil))
        }
      }

      Instances(
        instances.map(inst => inst.name.toString -> ((inst, m.getOrElse(inst.name.toString, Nil), true))).toMap,
        state.dict(TypeWrapper(primaryTpe)).name.toString
      )
    }
  }

  case class Instances(
    dict: Map[String, (Instance, List[String], Boolean)],
    root: String
  ) {
    import Instances._

    def prioritySubstitute: Option[Instances] =
      dict.iterator
        .map{case (k, v @ (inst, deps, canBeInlined)) => (k, v, priorityCanBeSubstituted((inst, deps)))}
        .collectFirst { case (k, (inst, dependees, canBeInlined), Some(tree)) =>
          copy(dict = dict.updated(k, (inst.copy(inst = Some(tree)), dependees, canBeInlined)))
        }

    def inline: Option[Instances] =
      dict.find{case (k, v @ (inst, deps, canBeInlined0)) => canBeInlined0 && k != root && canBeInlined((inst, deps)) } match {
        case None => None
        case Some((k, (inst, dependees, _))) =>
          assert(dependees.length == 1)
          val (dependeeInst, dependeeDependedOnBy, _) = dict(dependees.head)
          // assert(dependeeInst.dependsOn.contains(k)) // Change dependsOn element type
          val inliner = new Inliner(inst.name, inst.inst.get)
          val dependeeInst0 = inliner.transform(dependeeInst.inst.get)

          val dict0 =
            if (inliner.count == 1)
              (dict - k).updated(
                dependees.head,
                (
                  dependeeInst.copy(
                    dependsOn = dependeeInst.dependsOn.filterNot(_ =:= inst.instTpe),
                    inst = Some(dependeeInst0)
                  ),
                  dependeeDependedOnBy,
                  true
                )
              )
            else
              dict.updated(k, (inst, dependees, false))

          Some(copy(dict = dict0))
      }

    def optimize: Instances =
      prioritySubstitute.orElse(inline) match {
        case None =>
          this
        case Some(instances) =>
          instances.optimize
      }

    def repr: String =
      s"Instances($root,\n${dict.toList.sortBy(_._1).map(kv => s"  ${kv._1}:\n    ${kv._2._1}\n    ${kv._2._2}").mkString("\n")}\n)"
  }

  def mkInstances(state: LazyState)(primaryTpe: Type): (Tree, Type) = {
    val instances0 = Instances(state, primaryTpe)
    val instances1 = instances0.optimize

    val instances = instances1.dict.toList.map(_._2._1)
    val (from, to) = instances.map { d => (d.symbol, NoSymbol) }.unzip

    if (instances.length == 1) {
      val instance = instances.head
      import instance._
      inst match {
        case Some(inst) =>
          val cleanInst0 = c.untypecheck(c.internal.substituteSymbols(inst, from, to))
          val cleanInst = new StripUnApplyNodes().transform(cleanInst0)
          val tree = q" $cleanInst.asInstanceOf[$actualTpe] "
          (tree, actualTpe)
        case None =>
          abort(s"Uninitialized $instTpe lazy implicit")
      }
    } else {
      val instTrees =
        instances.map { instance =>
          import instance._
          inst match {
            case Some(inst) =>
              val cleanInst0 = c.untypecheck(c.internal.substituteSymbols(inst, from, to))
//              inst match {
//                case q"$method[..$tp](shapeless.Strict.apply[..$tpa]($something))" =>
//                  println(s"Matched: $something ($method, ${(something: Tree).tpe})")
//                case _ =>
//              }
              val cleanInst = new StripUnApplyNodes().transform(cleanInst0)
              q"""lazy val $name: $actualTpe = $cleanInst.asInstanceOf[$actualTpe]"""
            case None =>
              abort(s"Uninitialized $instTpe lazy implicit")
          }
        }

      val primaryInstance = state.lookup(primaryTpe).get.right.get
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
}
