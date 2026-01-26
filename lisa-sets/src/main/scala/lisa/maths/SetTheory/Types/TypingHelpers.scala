package lisa.maths.SetTheory.Types

//import lisa.maths.SetTheory.Base.Predef.{*, given}
//import lisa.maths.SetTheory.Functions.Predef.{*}
//import lisa.maths.SetTheory.Cardinal.Predef.{*}
//import lisa.maths.Quantifiers.*
import lisa.utils.prooflib._  
import lisa.utils.fol.FOL.{=== as _, ≠ as _, *, given}
import lisa.SetTheoryLibrary.{given, _}
/**
 * This file defines the most common variable symbols (x, y, z, etc.)
 * and their types for a consistent use through the Calculus of Construction
 * as well as some useful helper theorems used in the typing rules.
 * 
 * ## Syntactic Sugar
 * 
 * This file provides ergonomic syntax extensions for dependent type theory:
 * 
 * ### Type Membership
 * - `t is T` — type assignment (alias for `t ∈ T`)
 * - `t :: T` — type assignment (alias for `t ∈ T`)
 * 
 * ### Function Application
 * - `f @@ x` — function application (alias for `app(f)(x)`)
 * - `f * x` — function application (alias for `app(f)(x)`)
 * 
 * ### Function Types
 * - `A ->: B` — non-dependent function type (equivalent to `Π(x :: A). B` where x is fresh)
 * 
 * ### Dependent Types
 * - `Π(x :: A, B(x))` — dependent product type using VarTypeAssign
 * - `fun(x :: A, e(x))` — lambda abstraction using VarTypeAssign
 */

object TypingHelpers extends lisa.Main:
  import lisa.maths.SetTheory.Base.Predef.{*, given}
  import lisa.maths.SetTheory.Functions.Predef.{*}
  import lisa.maths.SetTheory.Cardinal.Predef.{*}
  import lisa.maths.Quantifiers.{*}

  // Enter next level of universe
  val Next = DEF(λ(U, universeOf(U)))  
  def getUniverse(n: Int, base: Expr[Ind]): Expr[Ind] = {
    if (n == 1) then base
    else universeOf(getUniverse(n - 1, base))
  }
  import lisa.maths.SetTheory.Functions.Predef.{app}
  // Base term
  val e1, e2 = variable[Ind]

  // Function
  val e = variable[Ind >>: Ind]

  // Base type
  val T, T1 = variable[Ind]

  // Dependent type
  val T2, T2p = variable[Ind >>: Ind]

  // Proposition
  val Q, H = variable[Ind >>: Prop]

  // Type Universe
  val U, U1, U2 = variable[Ind]

  // Proposition
  val p = variable[Prop]

  /**
   * Universe(Type) level
   */
  val Typ0 = variable[Ind]
  val typeOf = ∈

  type Typ = Expr[Ind] // | Expr[Ind >>: Prop]


  // Pattern extractor for the 'app' Shallow Embedding constant.
  // It allows matching expressions of the form app(func)(arg) using the pattern Sapp(func, arg)
  object Sapp:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case App(App(`app`, func), arg) =>
          Some((func.asInstanceOf[Expr[Ind]], arg.asInstanceOf[Expr[Ind]]))
        case _ => None

  // Type/Term abstraction λx:T.e <=> abs(T)(λx.e)
  val abs: Constant[Ind >>: (Ind >>: Ind) >>: Ind] = DEF(λ(T, λ(e, { (x, e(x)) | x ∈ T })))
    .printAs(args =>
      val typ = args(0)
      val (v, body) = args(1) match
        case Abs(v, b) => (v, b)
        case _ => (x, args(1))
      s"λ($v: $typ). $body"
    )
  class VarTypeAssign(val x: Variable[Ind], val typ: Expr[Ind]) extends App[Ind, Prop](∈(x), typ) {
    this : Expr[Prop] =>
  }
  extension (x: Variable[Ind]) {
    infix def ::(e: Expr[Ind]): VarTypeAssign & Expr[Prop] = VarTypeAssign(x, e)
    infix def is(e: Expr[Ind]) = VarTypeAssign(x, e)
  }

  inline given Conversion[VarTypeAssign, Expr[Prop]] with
    def apply(vta: VarTypeAssign): Expr[Prop] = vta


  def fun(v: VarTypeAssign, b: Expr[Ind]): Expr[Ind] = abs(v.typ)(λ(v.x, b))

  class CstTypeAssign(val c: Constant[Ind], val typ: Expr[Ind]) extends App[Ind, Prop](∈(c), typ)
  extension (c: Constant[Ind]) {
    infix def ::(e: Expr[Ind]) = CstTypeAssign(c, e)
    infix def is(e: Expr[Ind]) = CstTypeAssign(c, e)
  }

  // Pattern extractor for the 'abs' Shallow Embedding constant.
  // It allows matching expressions of the form abs(typ)(body) using the pattern Sabs(typ, body).
  object Sabs:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind >>: Ind])] =
      e match
        // We match against the specific Constant 'abs' being applied twice: App(App(abs, typ), body)
        case App(App(`abs`, typ), body) =>
          Some((typ.asInstanceOf[Expr[Ind]], body.asInstanceOf[Expr[Ind >>: Ind]]))
        case _ => None

  // Dependent productin type: Π(x:T1).T2
  val Pi: Constant[Ind >>: (Ind >>: Ind) >>: Ind] = DEF(
    λ(
      T1,
      λ(
        T2, {
          f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) |
            // f is a function
            (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\
            // f(a)'s type should be T2(a)
            (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a))))) //
        }
      )
    )
  ).printAs(args =>
    val ty1 = args(0)
    val (v, ty2) = args(1) match
      case Abs(v, body) => (v, body)
      case _ => (x, args(1))
    s"Π($v: $ty1). $ty2"
  )
  def `Π`(v: VarTypeAssign, b: Expr[Ind]): Expr[Ind] = Pi(v.typ)(λ(v.x, b))

  // Pattern extractor for the 'Pi' Shallow Embedding constant.
  // It allows matching expressions of the form Pi(T1)(T2) using the pattern SPi(T1, T2).
  object SPi:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind >>: Ind])] =
      e match
        // We match against the specific Constant 'Pi' being applied twice: App(App(Pi, T1), T2)
        case App(App(`Pi`, t1), t2) =>
          Some((t1.asInstanceOf[Expr[Ind]], t2.asInstanceOf[Expr[Ind >>: Ind]]))
        case _ => None

  object SArrow:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case SPi(t1, lambda(x, t2)) if !t2.freeVars.contains(x) =>
          Some((t1, t2))
        case _ => None

  // Pattern extractor for the `⊆` Shallow Embedding constant.
  // It allows matching expressions of the form ⊆(t1)(t2) using the pattern SUnion(t1, t2)
  object SUnion:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case App(App(`∪`, t1), t2) =>
          Some((t1.asInstanceOf[Expr[Ind]], t2.asInstanceOf[Expr[Ind]]))
        case _ => None

  /**
   * Notation `A ->: B <=> Π(x :: A). B`
   * where B is independent on x
   */
  extension (a: Expr[Ind]) {
    infix def ->:(b: Expr[Ind]): Expr[Ind] =
      Pi(a)(λ(x, b))
  }
  object `->:` :
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case SPi(a, lambda(x, b)) if !b.freeVars.contains(x) =>
          Some((a, b))
        case _ => None

  // ============================================================================
  // Syntactic Sugar Extensions (OldTypeSystem compatibility layer)
  // ============================================================================

  /**
   * Type membership operators (aliases for ∈)
   * 
   * Usage:
   *   t is T  // equivalent to t ∈ T
   *   t :: T  // equivalent to t ∈ T (for general terms, not just variables)
   */
  extension (t: Expr[Ind]) {
    infix def is(typ: Expr[Ind]): Expr[Prop] = t ∈ typ
    // Note: :: for general terms (variables already have :: via VarTypeAssign)
    infix def `::`(typ: Expr[Ind]): Expr[Prop] = t ∈ typ
  }

  /**
   * Function application operators (aliases for app)
   * 
   * Usage:
   *   f @@ x  // equivalent to app(f)(x)
   *   f * x   // equivalent to app(f)(x)
   */
  extension (f: Expr[Ind]) {
    infix def @@(arg: Expr[Ind]): Expr[Ind] = app(f)(arg)
    infix def *(arg: Expr[Ind]): Expr[Ind] = app(f)(arg)
  }
  object * {
    private val multi_app = Multiapp(app)
    def unapply(t: Expr[Ind]): Option[(Expr[Ind], Expr[Ind])] = app.unapply2(t)
  }


  // ============================================================================
  // Typed Constants
  // ============================================================================

  class TypedConstant
    (id: Identifier, val typ: Typ, val justif: JUSTIFICATION) extends Constant[Ind](id) {
    val formula = CstTypeAssign(this, typ)
    assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))

    override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): TypedConstant = this
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): TypedConstant =
      super.substituteWithCheck(m).asInstanceOf[TypedConstant]
    override def substitute(pairs: SubstPair*): TypedConstant =
      super.substitute(pairs*).asInstanceOf[TypedConstant]
  }


  def optype(t: Option[Typ], member: Expr[Ind]): Expr[Prop] = t match
    case Some(typ) => member is typ
    case None => top

  case class FunctionalClass(inTyp: List[Option[Typ]], args: List[Variable[Ind]], outTyp: Typ) {
    def formula(f: Expr[?]): Expr[Prop] = {
      val inner = (args.zip(inTyp).map((term, inType) => optype(inType, term)
        ).reduceLeft[Expr[Prop]]((a, b) => a /\ b)) ==> ((f #@@ args).asInstanceOf[Expr[Ind]] `is` outTyp)
      args.foldRight(inner)((v, form) => forall(v, form))
    }

    def formulaMinusOne(f: Constant[?]): Expr[Prop] = {
      val inner = (args.zip(inTyp).map((term, inType) => optype(inType, term)
        ).reduceLeft[Expr[Prop]]((a, b) => a /\ b)) ==> ((f #@@ args).asInstanceOf[Expr[Ind]] `is` outTyp)
      args.tail.foldRight(inner)((v, form) => forall(v, form))
    }
  }

  class FunctionalTypeAssign[S](
    const: Constant[S],
    typ: FunctionalClass
  ) extends App[Ind>>:Prop, Prop](forall, λ(typ.args.head, typ.formulaMinusOne(const))) {
  }

  class TypedConstantFunctional[S: Sort]
    (id: Identifier, val typ: FunctionalClass, val justif: JUSTIFICATION) extends Constant[S](id) {
    assert(typ.inTyp.size == arity)

    override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): TypedConstantFunctional[S] = this
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): TypedConstantFunctional[S] =
      super.substituteWithCheck(m).asInstanceOf[TypedConstantFunctional[S]]
    override def substitute(pairs: SubstPair*): TypedConstantFunctional[S] =
      super.substitute(pairs*).asInstanceOf[TypedConstantFunctional[S]]
    
  }

  ///////////////////////
  ///// Definitions /////
  ///////////////////////


  class TypedSimpleConstantDefinition(using om: OutputManager)(fullName: String, line: Int, file: String)(
      val expression: Expr[Ind],
      val typ:Typ
  ) extends DirectDefinition[Ind](fullName, line, file)(expression, Seq[Variable[?]]()) {
    val typingName = "typing_" + fullName
    val typingJudgement = THM( cst :: typ, typingName, line, file, InternalStatement)({
      //have(expression :: typ) by TypeChecker.prove
      //thenHave(thesis) by lisa.automation.Substitution.ApplyRules(getShortDefinition(cst).get) //TODO
    })
    val typedLabel: TypedConstant = TypedConstant(cst.id, typ, typingJudgement)


  }

  def TYPEDEF(
          using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(term:Expr[Ind], typ: Typ): TypedConstant =
      TypedSimpleConstantDefinition(name.value, line.value, file.value)(term, typ).typedLabel


  extension (c: Constant[Ind]) {
    def typedWith(typ:Typ)(justif: JUSTIFICATION) : TypedConstant =
      if justif.statement.right.size != 1  || justif.statement.left.size != 0 || !K.isSame((c `is` typ).underlying, justif.statement.right.head.underlying) then
        throw new IllegalArgumentException(s"A proof of typing of $c must be of the form ${c :: typ}, but the given justification shows ${justif.statement}.")
      else TypedConstant(c.id, typ, justif)
  }



