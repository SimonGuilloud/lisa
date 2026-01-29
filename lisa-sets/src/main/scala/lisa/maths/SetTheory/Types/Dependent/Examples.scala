package lisa.maths.SetTheory.Types.Dependent

import Symbols.*
import Tactics.*
import TypingRules.*

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.{*, given}
import lisa.maths.SetTheory.Cardinal.Predef.{isUniverse}

object Examples extends lisa.Main:
  private val Typ = variable[Ind]
  private val Typ2 = getUniverse(2, Typ)
  private val Typ3 = getUniverse(3, Typ)
  private val Typ4 = getUniverse(4, Typ)
  private val Typ5 = getUniverse(5, Typ)
  private val Nat, Int, Bool, String, Real = variable[Ind]
  private val A, B, C, T = variable[Ind]
  private val f, g, x, y, a, s, t, n, m = variable[Ind]
  private val tru, fls = variable[Ind]

  ////////////////////////////////
  //////// Basic Tests ///////////
  ////////////////////////////////

  // Identity function
  val test0_identity = Theorem(a ∈ Nat |- fun(x :: Nat, x)(a) ∈ Nat) {
    have(thesis) by Typecheck.prove
  }
  // Curried function
  val test1_curried = Theorem(s ∈ String |- fun(x :: Nat, fun(y :: Bool, s)) ∈ (Nat ->: (Bool ->: String))) {
    have(thesis) by Typecheck.prove
  }
  // Composition function
  val test2_composition = Theorem((f ∈ (A ->: B), g ∈ (B ->: C), a ∈ A) |- g(f(a)) ∈ C) {
    have(thesis) by Typecheck.prove
  }
  // Dependent function
  val test3_dependent = Theorem(Nat ∈ Typ |- fun(x :: Typ, fun(y :: x, y))(Nat) ∈ Π(y :: Nat, Nat)) {
    have(thesis) by Typecheck.prove
  }
  // Nested Polymorphic Projection
  val test4_nested_polymorphic_projection = Theorem(
    (a ∈ Nat, b ∈ Nat, Nat ∈ Typ) |-
      fun(T :: Typ, fun(x :: T, fun(y :: T, x)))(Nat, a, b) ∈ Nat
  ) {
    have(thesis) by Typecheck.prove
  }

  // Nested Polymorphic function
  val doublePolyTerm = fun(A :: Typ, fun(B :: Typ, fun(f :: (A ->: B), fun(a :: A, f(a)))))
  val doublePolyType = Π(A :: Typ, Π(B :: Typ, Π(f :: A ->: B, Π(a :: A, B))))
  val test5_doublePoly = Theorem(
    doublePolyTerm ∈ doublePolyType
  ) {
    have(thesis) by Typecheck.prove
  }
  val test5_doublePolyApp = Theorem(
    (Nat ∈ Typ, Bool ∈ Typ, n ∈ Nat, tru ∈ Bool) |-
      doublePolyTerm(Nat, Bool, fun(x :: Nat, tru), n) ∈ Bool
  ) {
    have(thesis) by Typecheck.prove
  }

  ///////////////////////////////////////////////
  ///////// Relative Complicated Tests //////////
  ///////////////////////////////////////////////

  /**
   * Test1: S.K.I combinator
   */
  val STerm = fun(f :: (A ->: A ->: A), fun(g :: (A ->: A), fun(x :: A, f(x)(g(x)))))
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
  val test_SKI = Theorem(a ∈ A |- STerm(KTerm, ITerm, a) ∈ A) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 2: Church Encodings (Complex Logic)
   */
  // Church Bool Type: Π(A: Typ). A -> A -> A
  val CBool = Π(A :: Typ, A ->: A ->: A)

  // Church True: λA. λx. λy. x
  val CTrue = fun(A :: Typ, fun(x :: A, fun(y :: A, x)))

  // Church False: λA. λx. λy. y
  val CFalse = fun(A :: Typ, fun(x :: A, fun(y :: A, y)))

  // Verify True has type Bool
  val test_ChurchTrue = Theorem(
    isUniverse(Typ) |- CTrue ∈ CBool
  ) {
    have(thesis) by Typecheck.prove
  }

  // NOT = λb: Bool. λA: Typ. λx: A. λy: A. b A y x
  // This tests passing a "Function" (b) as an argument and applying it
  val CNot = fun(b :: CBool, fun(A :: Typ, fun(x :: A, fun(y :: A, b(A, y, x)))))

  // Verify NOT True == False (Type level check)
  val test_ChurchLogic = Theorem(
    isUniverse(Typ) |- CNot(CTrue) ∈ CBool
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 3: Church Number (Complex Logic)
   */
  val CNat = Π(A :: Typ, (A ->: A) ->: A ->: A)
  val zero = fun(A :: Typ, fun(f :: (A ->: A), fun(x :: A, x)))
  val succ = fun(n :: CNat, fun(A :: Typ, fun(f :: (A ->: A), fun(x :: A, f(n(A, f, x))))))

  val test_Zero = Theorem(isUniverse(Typ) |- zero ∈ CNat) {
    have(thesis) by Typecheck.prove
  }

  // 1 = succ(0)
  val one = succ(zero)
  val test_One = Theorem(isUniverse(Typ) |- one ∈ CNat) {
    have(thesis) by Typecheck.prove
  }

  // Church Addition: λn. λm. λA. λf. λx. n A f (m A f x)
  val plus = fun(n :: CNat, fun(m :: CNat, fun(A :: Typ, fun(f :: (A ->: A), fun(x :: A, n(A, f, m(A, f, x)))))))

  // 1 + 0 = 1
  val test_Add = Theorem(isUniverse(Typ) |- plus(one, zero) ∈ CNat) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test4: Polymorphic Identity(Hierachy Promotion)
   */
  val PolyId_0 = fun(X :: Typ, fun(x :: X, x))
  val PolyIdType_0 = Π(T :: Typ, T ->: T)
  val PolyId_1 = fun(X :: Typ2, fun(x :: X, x))
  val PolyIdType_1 = Π(X :: Typ2, X ->: X)
  val testBasic = Theorem(PolyId_0 ∈ PolyIdType_0) {
    have(thesis) by Typecheck.prove
  }
  val testPoly = Theorem(PolyId_1 ∈ PolyIdType_1) {
    have(thesis) by Typecheck.prove
  }
  val testPolyPrime = Theorem(isUniverse(Typ) |- PolyId_1(PolyIdType_0) ∈ Π(x :: PolyIdType_0, PolyIdType_0)) {
    have(thesis) by Typecheck.prove
  }
  val test_SelfApp = Theorem(isUniverse(Typ) |- PolyId_1(PolyIdType_0, PolyId_0) ∈ PolyIdType_0) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 5: Dependent Subsumption
   */
  val z = variable[Ind]
  val SuperId = fun(X :: Typ2, fun(x :: X, x))
  val test_Grandfather = Theorem(
    (isUniverse(Typ), Nat ∈ Typ, z ∈ Nat) |-
      SuperId(Nat, z) ∈ Nat
  ) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test 6: Galaxy Bridge(Multi-Level Dependency)
   */
  val GalaxyBridgeTerm = fun(A :: Typ, fun(B :: Typ2, fun(C :: Typ3, A ->: B ->: C)))
  val GalaxyBridgeType = Π(A :: Typ, Π(B :: Typ2, Π(C :: Typ3, Typ3)))
  val test_Galaxy_term = Theorem(
    isUniverse(Typ) |- GalaxyBridgeTerm ∈ GalaxyBridgeType
  ) {
    have(thesis) by Typecheck.prove
  }
  val test_Galaxy_Type_Level = Theorem(
    isUniverse(Typ) |- GalaxyBridgeType ∈ Typ4
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
  val poly_f = fun(A :: Typ, fun(x :: A, fun(y :: A, y)))
  val PolyTerm = poly_f(Nat, n, n)
  val test10_PolymorphicContravariance = Theorem(
    (isUniverse(Typ), n ∈ Nat, Nat ∈ Typ, Nat ⊆ Int) |- PolyTerm ∈ Int
  ) {
    have(thesis) by Typecheck.prove
  }

  ///////////////////////////////////////////////
  ///////// Case Study: Function.left_id ////////
  ///////////////////////////////////////////////

  // Lean: id : Π(A:Type). A → A
  val Id = fun(X :: Typ5, fun(x :: X, x))
  val IdType = Π(X :: Typ5, X ->: X)

  // Lean: comp : Π(A B C). (B → C) → (A → B) → A → C
  val Comp =
    fun(A :: Typ5, fun(B :: Typ5, fun(C :: Typ5, fun(g :: (B ->: C), fun(f :: (A ->: B), fun(a :: A, g(f(a))))))))

  val CompType =
    Π(A :: Typ5, Π(B :: Typ5, Π(C :: Typ5, (B ->: C) ->: (A ->: B) ->: A ->: C)))

  // Sanity checks
  val test_Id = Theorem(Id ∈ IdType) {
    have(thesis) by Typecheck.prove
  }

  val test_Comp = Theorem(
    isUniverse(Typ) |- Comp ∈ CompType
  ) {
    have(thesis) by Typecheck.prove
  }

  val test_id_comp = Theorem(
    (isUniverse(Typ), A ∈ Typ, B ∈ Typ3, f ∈ (A ->: B)) |-
      Comp(A, B, B, Id(B), f) ∈ (A ->: B)
  ) {
    have(thesis) by Typecheck.prove
  }
