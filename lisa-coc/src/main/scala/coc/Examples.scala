package cic

import Symbols.*
import Tactics.*
import TypingRules.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.{*}
import lisa.maths.SetTheory.Cardinal.Predef.{isUniverse}
import cic.Tactics.Typecheck
import cic.Tactics.Typecheck

object Examples extends lisa.Main:
  private val Typ0 = variable[Ind]
  private val Typ2 = getUniverse(2, Typ0)
  private val Typ3 = getUniverse(3, Typ0)
  private val Typ4 = getUniverse(4, Typ0)
  private val Nat, Int, Bool, String, Real = variable[Ind]
  private val A, B, C, T = variable[Ind]
  private val f, g, x, y, a, s, t, n, m = variable[Ind]
  private val tru, fls = variable[Ind]

  ////////////////////////////////
  //////// Basic Tests ///////////
  ////////////////////////////////

  // Identity function
  val test0_identity = Theorem(a ∈ Nat |- app(fun(x :: Nat, x))(a) ∈ Nat) {
    have(thesis) by Typecheck.prove
  }
  // Curried function
  val test1_curried = Theorem(s ∈ String |- fun(x :: Nat, fun(y :: Bool, s)) ∈ (Nat ->: (Bool ->: String))) {
    have(thesis) by Typecheck.prove
  }
  // Composition function
  val test2_composition = Theorem((f ∈ (A ->: B), g ∈ (B ->: C), a ∈ A) |- app(g)(app(f)(a)) ∈ C) {
    have(thesis) by Typecheck.prove
  }
  // Dependent function
  val test3_dependent = Theorem(Nat ∈ Typ0 |- app(fun(x :: Typ0, fun(y :: x, y)))(Nat) ∈ Π(y :: Nat, Nat)) {
    have(thesis) by Typecheck.prove
  }
  // Nested Polymorphic Projection
  val test4_nested_polymorphic_projection = Theorem(
    (a ∈ Nat, b ∈ Nat, Nat ∈ Typ0) |-
      app(app(app(fun(T :: Typ0, fun(x :: T, fun(y :: T, x))))(Nat))(a))(b) ∈ Nat
  ) {
    have(thesis) by Typecheck.prove
  }

  // Nested Polymorphic function
  val doublePolyTerm = fun(A :: Typ0, fun(B :: Typ0, fun(f :: (A ->: B), fun(a :: A, app(f)(a)))))
  val doublePolyType = Π(A :: Typ0, Π(B :: Typ0, Π(f :: A ->: B, Π(a :: A, B))))
  val test5_doublePoly = Theorem(
    doublePolyTerm ∈ doublePolyType
  ) {
    have(thesis) by Typecheck.prove
  }
  val test5_doublePolyApp = Theorem(
    (Nat ∈ Typ0, Bool ∈ Typ0, n ∈ Nat, tru ∈ Bool) |-
      app(app(app(app(doublePolyTerm)(Nat))(Bool))(fun(x :: Nat, tru)))(n) ∈ Bool
  ) {
    have(thesis) by Typecheck.prove
  }

  ///////////////////////////////////////////////
  ///////// Relative Complicated Tests //////////
  ///////////////////////////////////////////////

  /**
   * Test1: S.K.I combinator
   */
  val STerm = fun(f :: (A ->: A ->: A), fun(g :: (A ->: A), fun(x :: A, app(app(f)(x))(app(g)(x)))))
  val SType = (A ->: A ->: A) ->: (A ->: A) ->: A ->: A
  val KTerm = fun(x :: A, fun(y :: A, x))
  val KType = A ->: A ->: A
  val ITerm = fun(x :: A, x)
  val IType = A ->: A
  val testS = Theorem(STerm ∈ SType) {
    have(thesis) by Typecheck.prove
  }
  val testK = Theorem(KTerm ∈ KType) {
    have(thesis) by Typecheck.prove
  }
  val testI = Theorem(ITerm ∈ IType) {
    have(thesis) by Typecheck.prove
  }
  val test_SKI = Theorem(a ∈ A |- app(app(app(STerm)(KTerm))(ITerm))(a) ∈ A) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 2: Church Encodings (Complex Logic)
   */
  // Church Bool Type: Π(A: Typ0). A -> A -> A
  val CBool = Π(A :: Typ0, A ->: A ->: A)

  // Church True: λA. λx. λy. x
  val CTrue = fun(A :: Typ0, fun(x :: A, fun(y :: A, x)))

  // Church False: λA. λx. λy. y
  val CFalse = fun(A :: Typ0, fun(x :: A, fun(y :: A, y)))

  // Verify True has type Bool
  val test_ChurchTrue = Theorem(
    isUniverse(Typ0) |- CTrue ∈ CBool
  ) {
    have(thesis) by Typecheck.prove
  }

  // NOT = λb: Bool. λA: Typ0. λx: A. λy: A. b A y x
  // This tests passing a "Function" (b) as an argument and applying it
  val CNot = fun(b :: CBool, fun(A :: Typ0, fun(x :: A, fun(y :: A, app(app(app(b)(A))(y))(x)))))

  // Verify NOT True == False (Type level check)
  val test_ChurchLogic = Theorem(
    isUniverse(Typ0) |- app(CNot)(CTrue) ∈ CBool
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 3: Church Number (Complex Logic)
   */
  val CNat = Π(A :: Typ0, (A ->: A) ->: A ->: A)
  val zero = fun(A :: Typ0, fun(f :: (A ->: A), fun(x :: A, x)))
  val succ = fun(n :: CNat, fun(A :: Typ0, fun(f :: (A ->: A), fun(x :: A, app(f)(app(app(app(n)(A))(f))(x))))))

  val test_Zero = Theorem(isUniverse(Typ0) |- zero ∈ CNat) {
    have(thesis) by Typecheck.prove
  }

  // 1 = succ(0)
  val one = app(succ)(zero)
  val test_One = Theorem(isUniverse(Typ0) |- one ∈ CNat) {
    have(thesis) by Typecheck.prove
  }

  // Church Addition: λn. λm. λA. λf. λx. n A f (m A f x)
  val plus = fun(n :: CNat, fun(m :: CNat, fun(A :: Typ0, fun(f :: (A ->: A), fun(x :: A, app(app(app(n)(A))(f))(app(app(app(m)(A))(f))(x)))))))

  // 1 + 0 = 1
  val test_Add = Theorem(isUniverse(Typ0) |- app(app(plus)(one))(zero) ∈ CNat) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test4: Polymorphic Identity(Hierachy Promotion)
   */
  val PolyId_0 = fun(X :: Typ0, fun(x :: X, x))
  val PolyIdType_0 = Π(T :: Typ0, T ->: T)
  val PolyId_1 = fun(X :: Typ2, fun(x :: X, x))
  val PolyIdType_1 = Π(X :: Typ2, X ->: X)
  val testBasic = Theorem(PolyId_0 ∈ PolyIdType_0) {
    have(thesis) by Typecheck.prove
  }
  val testPoly = Theorem(PolyId_1 ∈ PolyIdType_1) {
    have(thesis) by Typecheck.prove
  }
  val testPolyPrime = Theorem(isUniverse(Typ0) |- app(PolyId_1)(PolyIdType_0) ∈ Π(x :: PolyIdType_0, PolyIdType_0)) {
    have(thesis) by Typecheck.prove
  }
  val test_SelfApp = Theorem(isUniverse(Typ0) |- app(app(PolyId_1)(PolyIdType_0))(PolyId_0) ∈ PolyIdType_0) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 5: Dependent Subsumption
   */
  val z = variable[Ind]
  val SuperId = fun(X :: Typ2, fun(x :: X, x))
  val test_Grandfather = Theorem(
    (isUniverse(Typ0), Nat ∈ Typ0, z ∈ Nat) |-
      app(app(SuperId)(Nat))(z) ∈ Nat
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 6: Galaxy Bridge(Multi-Level Dependency)
   */
  val GalaxyBridgeTerm = fun(A :: Typ0, fun(B :: Typ2, fun(C :: Typ3, A ->: B ->: C)))
  val GalaxyBridgeType = Π(A :: Typ0, Π(B :: Typ2, Π(C :: Typ3, Typ3)))
  val test_Galaxy_term = Theorem(
    isUniverse(Typ0) |- GalaxyBridgeTerm ∈ GalaxyBridgeType
  ) {
    have(thesis) by Typecheck.prove
  }
  val test_Galaxy_Type_Level = Theorem(
    isUniverse(Typ0) |- GalaxyBridgeType ∈ Typ4
  ) {
    have(thesis) by Typecheck.prove
  }

  ///////////////////////////////////////////////
  /////////   Semantic Subset Tests    //////////
  ///////////////////////////////////////////////
  /**
   * Test 7: Simple Data Subtyping
   */
  val test7_DataSubtyping = Theorem(
    (n ∈ Nat, Nat ⊆ Int) |- n ∈ Int
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 8: Function Codomain Covariance
   * Verifies that (A -> Nat) is a subtype of (A -> Int).
   */
  val test8_FuncCovariance = Theorem(
    (f ∈ (A ->: Nat), Nat ⊆ Int) |- f ∈ (A ->: Int)
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 9: Deeply Nested Pi Covariance
   * Verifies subtyping logic propagates through multiple layers of function bodies.
   */
  val DeepTerm = fun(x :: A, fun(y :: B, fun(z :: C, a)))
  val DeepTargetType = A ->: B ->: C ->: Real
  val test9_DeepNested = Theorem(
    (a ∈ Nat, Nat ⊆ Real) |- DeepTerm ∈ DeepTargetType
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 10: Polymorphic Instantiation & Subtyping
   * Verifies that the result of a polymorphic application (Nat) satisfies the supertype Int.
   */
  val poly_f = fun(A :: Typ0, fun(x :: A, fun(y :: A, y)))
  val PolyTerm = app(app(app(poly_f)(Nat))(n))(n)
  val test10_PolymorphicContravariance = Theorem(
    (isUniverse(Typ0), n ∈ Nat, Nat ∈ Typ0, Nat ⊆ Int) |- PolyTerm ∈ Int
  ) {
    have(thesis) by Typecheck.prove
  }
