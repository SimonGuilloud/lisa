package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}
import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.{InitialSegment, WellOrder}
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation

/**
 * Exponentiation on naturals, defined by recursion on the exponent.
 *
 * Isabelle/HOL reference: `IsabelleHOL/Power.thy` (specialized to nat multiplication).
 */
object NatPower extends lisa.Main {

  private val Pred = variable[Ind >>: Prop]

  private val a = variable[Ind]
  private val b = variable[Ind]
  private val m = variable[Ind]
  private val n = variable[Ind]
  private val k = variable[Ind]
  private val x = variable[Ind]
  private val h = variable[Ind]
  private val y = variable[Ind]

  // Local copy (structurally identical to Nat's) to avoid accessing Nat.memRel (which is private).
  private val memRel = MembershipRelation.membershipRelation(ℕ)

  /** Exponentiation: `pow(a)(n) = a^n` with recursion equations `a^0 = 1` and `a^(Succ n) = a^n * a`. */
  val pow = DEF(
    λ(a,
      λ(n,
        app(
          Necessary.recursiveFunctionOn(
            λ(x,
              λ(h,
                ε(y,
                  ((x === 0) /\ (y === 1)) \/
                    ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === app(h)(k) * a))
                )
              )
            )
          )(ℕ)(memRel)
        )(n)
      )
    )
  ).printInfix("^")

  extension (a: Expr[Ind])
    infix def ^(n: Expr[Ind]): Expr[Ind] = pow(a)(n)

  /** Lemma: recursion equation `a^0 = 1`. */
  val powZero = Theorem((a ^ 0) === 1) {
    val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(Nat.natWellOrder))

    val F = λ(x,
      λ(h,
        ε(y,
          ((x === 0) /\ (y === 1)) \/
            ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === app(h)(k) * a))
        )
      )
    )

    val G = Necessary.recursiveFunctionOn(F)(ℕ)(memRel)

    val spec = have(
      functionOn(G)(ℕ) /\
        ∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
    ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := F)))

    val eqAll = have(∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))).by(Tautology.from(spec))

    val eq0 = have(0 ∈ ℕ |- app(G)(0) === F(0)(G ↾ InitialSegment.initialSegment(0)(ℕ)(memRel))).by(
      InstantiateForall(0)(eqAll)
    )

    val init0 = have(0 ∈ ℕ |- InitialSegment.initialSegment(0)(ℕ)(memRel) === 0).by(
      Restate.from(Nat.natInitialSegment.of(n := 0))
    )

    val eq0r = have(0 ∈ ℕ |- app(G)(0) === F(0)(G ↾ 0)).by(Substitute(init0)(eq0))

    val Q = λ(y,
      ((0 === 0) /\ (y === 1)) \/
        ∃(k, (k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a))
    )

    val F0 = have(F(0)(G ↾ 0) === ε(y, Q(y))).by(Restate)

    val exY = have(∃(y, Q(y))) subproof {
      val zRefl = have(0 === 0).by(Restate)
      val oneRefl = have(1 === 1).by(Restate)
      have(Q(1)).by(Tautology.from(zRefl, oneRefl))
      thenHave(thesis).by(RightExists)
    }

    val uniq = have(∀(y, Q(y) ==> (y === 1))) subproof {
      have(Q(y) |- y === 1) subproof {
        assume(Q(y))

        val case1 = have((0 === 0) /\ (y === 1) |- y === 1).by(Tautology)
        val case1Imp = have(((0 === 0) /\ (y === 1)) ==> (y === 1)).by(Restate.from(case1))

        val case2 = have(
          ∃(k, (k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a)) |- y === 1
        ) subproof {
          assume(∃(k, (k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a)))

          have((k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a) |- y === 1) subproof {
            val kInℕ = have((k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a) |- k ∈ ℕ).by(Tautology)
            val zEqSk = have((k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a) |- 0 === Succ(k)).by(Tautology)
            val not0EqSk = have((k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a) |- ¬(0 === Succ(k))).by(
              Tautology.from(Nat.zeroNeSucc.of(n := k), kInℕ)
            )
            have(thesis).by(Tautology.from(zEqSk, not0EqSk))
          }
          thenHave(∃(k, (k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a)) |- y === 1).by(LeftExists)
        }

        val case2Imp = have(∃(k, (k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a)) ==> (y === 1)).by(Restate.from(case2))

        val disj = have(((0 === 0) /\ (y === 1)) \/ ∃(k, (k ∈ ℕ) /\ (0 === Succ(k)) /\ (y === app(G ↾ 0)(k) * a))).by(Restate)

        have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
      }
      thenHave(Q(y) ==> (y === 1)).by(Restate)
      thenHave(thesis).by(RightForall)
    }

    val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

    val epsEq = have(ε(y, Q(y)) === 1) subproof {
      have(∀(y, Q(y) ==> (y === 1))).by(Restate.from(uniq))
      thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === 1)).by(InstantiateForall(ε(y, Q(y))))
      have(thesis).by(Tautology.from(epsQ, lastStep))
    }

    val powDef0 = have((a ^ 0) === app(G)(0)).by(Restate.from(pow.definition.of(a := a, n := 0)))

    val rhsEq1 = have(F(0)(G ↾ 0) === 1).by(Congruence.from(F0, epsEq))

    val rec0 = have(0 ∈ ℕ |- ((a ^ 0) === 1)).by(Congruence.from(powDef0, eq0r, rhsEq1))

    have(thesis).by(Cut(Nat.zeroInℕ, rec0))
  }

  /** Lemma: recursion equation `a^(Succ(n)) = a^n * a` for `n ∈ ℕ`. */
  val powSucc = Theorem(n ∈ ℕ |- ((a ^ Succ(n)) === ((a ^ n) * a))) {
    val nInℕ = assume(n ∈ ℕ)

    val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(Nat.natWellOrder))

    val F = λ(x,
      λ(h,
        ε(y,
          ((x === 0) /\ (y === 1)) \/
            ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === app(h)(k) * a))
        )
      )
    )

    val G = Necessary.recursiveFunctionOn(F)(ℕ)(memRel)

    val spec = have(
      functionOn(G)(ℕ) /\
        ∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
    ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := F)))

    val GOn = have(functionOn(G)(ℕ)).by(Tautology.from(spec))

    val eqAll = have(∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))).by(Tautology.from(spec))

    val SnInℕ = have(Succ(n) ∈ ℕ).by(Cut(nInℕ, Nat.succClosed.of(n := n)))

    val eqSn = have(
      Succ(n) ∈ ℕ |- app(G)(Succ(n)) === F(Succ(n))(G ↾ InitialSegment.initialSegment(Succ(n))(ℕ)(memRel))
    ).by(InstantiateForall(Succ(n))(eqAll))

    val initSn = have(Succ(n) ∈ ℕ |- InitialSegment.initialSegment(Succ(n))(ℕ)(memRel) === Succ(n)).by(
      Restate.from(Nat.natInitialSegment.of(n := Succ(n)))
    )

    val eqSnr = have(Succ(n) ∈ ℕ |- app(G)(Succ(n)) === F(Succ(n))(G ↾ Succ(n))).by(Substitute(initSn)(eqSn))

    val hSn = G ↾ Succ(n)

    val Q = λ(y,
      ((Succ(n) === 0) /\ (y === 1)) \/
        ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a))
    )

    val FSn = have(F(Succ(n))(hSn) === ε(y, Q(y))).by(Restate)

    val exY = have(∃(y, Q(y))) subproof {
      val SnEqSn = have(Succ(n) === Succ(n)).by(Restate)
      val rhsRefl = have((app(hSn)(n) * a) === (app(hSn)(n) * a)).by(Restate)
      have((n ∈ ℕ) /\ (Succ(n) === Succ(n)) /\ ((app(hSn)(n) * a) === (app(hSn)(n) * a))).by(Tautology.from(nInℕ, SnEqSn, rhsRefl))
      thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ ((app(hSn)(n) * a) === (app(hSn)(k) * a)))).by(RightExists)
      thenHave(Q(app(hSn)(n) * a)).by(Tautology)
      thenHave(thesis).by(RightExists)
    }

    val uniq = have(∀(y, Q(y) ==> (y === app(hSn)(n) * a))) subproof {
      have(Q(y) |- y === app(hSn)(n) * a) subproof {
        assume(Q(y))

        val SnNe0 = have(Succ(n) =/= 0).by(Tautology.from(nInℕ, Nat.succNeZero.of(n := n)))
        val notSnEq0 = have(¬(Succ(n) === 0)).by(Tautology.from(SnNe0))

        val case1 = have((Succ(n) === 0) /\ (y === 1) |- y === app(hSn)(n) * a) subproof {
          val SnEq0 = have((Succ(n) === 0) /\ (y === 1) |- Succ(n) === 0).by(Tautology)
          val notSnEq0Under = have((Succ(n) === 0) /\ (y === 1) |- ¬(Succ(n) === 0)).by(Weakening(notSnEq0))
          val contra = have((Succ(n) === 0) /\ (y === 1) |- ()).by(Tautology.from(SnEq0, notSnEq0Under))
          have(thesis).by(Weakening(contra))
        }
        val case1Imp = have(((Succ(n) === 0) /\ (y === 1)) ==> (y === app(hSn)(n) * a)).by(Restate.from(case1))

        val case2 = have(
          ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a)) |- y === app(hSn)(n) * a
        ) subproof {
          assume(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a)))

          have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a) |- y === app(hSn)(n) * a) subproof {
            val SnEqSk = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a) |- Succ(n) === Succ(k)).by(Tautology)
            val yEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a) |- y === app(hSn)(k) * a).by(Tautology)

            val inj = have(Succ(n) === Succ(k) |- n === k).by(Tautology.from(Nat.succInjective.of(m := n, n := k)))
            val nEqk = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a) |- n === k).by(Cut(SnEqSk, inj))
            val kEqn = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a) |- k === n).by(Congruence.from(nEqk))

            val appEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a) |- app(hSn)(k) * a === app(hSn)(n) * a).by(
              Congruence.from(kEqn)
            )

            val trans = have((y === app(hSn)(k) * a, app(hSn)(k) * a === app(hSn)(n) * a) |- y === app(hSn)(n) * a).by(Congruence)
            have(thesis).by(Tautology.from(trans, yEq, appEq))
          }
          thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a)) |- y === app(hSn)(n) * a).by(LeftExists)
        }

        val case2Imp = have(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a)) ==> (y === app(hSn)(n) * a)).by(Restate.from(case2))

        val disj = have(((Succ(n) === 0) /\ (y === 1)) \/ ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === app(hSn)(k) * a))).by(Restate)

        have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
      }
      thenHave(Q(y) ==> (y === app(hSn)(n) * a)).by(Restate)
      thenHave(thesis).by(RightForall)
    }

    val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

    val epsEq = have(ε(y, Q(y)) === app(hSn)(n) * a) subproof {
      have(∀(y, Q(y) ==> (y === app(hSn)(n) * a))).by(Restate.from(uniq))
      thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === app(hSn)(n) * a)).by(InstantiateForall(ε(y, Q(y))))
      have(thesis).by(Tautology.from(epsQ, lastStep))
    }

    val hSnAtN = have(app(hSn)(n) === app(G)(n)) subproof {
      val nSubℕ = have(n ⊆ ℕ).by(Cut(nInℕ, Nat.`n ∈ ℕ -> n ⊆ ℕ`))
      val SnInℕ2 = have(Succ(n) ∈ ℕ).by(Cut(nInℕ, Nat.succClosed.of(n := n)))
      val SnSubℕ = have(Succ(n) ⊆ ℕ).by(Cut(SnInℕ2, Nat.`n ∈ ℕ -> n ⊆ ℕ`.of(n := Succ(n))))
      val nInSn = have(n ∈ Succ(n)).by(Weakening(Nat.nInSucc.of(n := n)))
      val restEq = have((functionOn(G)(ℕ), Succ(n) ⊆ ℕ, n ∈ Succ(n)) |- app(G ↾ Succ(n))(n) === app(G)(n)).by(
        Restate.from(Necessary.restrictionAppSubset.of(f := G, A := ℕ, B := Succ(n), x := n))
      )
      have(thesis).by(Tautology.from(restEq, GOn, SnSubℕ, nInSn))
    }

    val rhs1 = have(F(Succ(n))(hSn) === app(hSn)(n) * a).by(Congruence.from(FSn, epsEq))
    val rhs2 = have(app(hSn)(n) * a === app(G)(n) * a).by(Congruence.from(hSnAtN))

    val trans = have((F(Succ(n))(hSn) === app(hSn)(n) * a, app(hSn)(n) * a === app(G)(n) * a) |- F(Succ(n))(hSn) === app(G)(n) * a).by(Congruence)
    val rhsEq = have(F(Succ(n))(hSn) === app(G)(n) * a).by(Tautology.from(trans, rhs1, rhs2))

    val powDefSn = have((a ^ Succ(n)) === app(G)(Succ(n))).by(Restate.from(pow.definition.of(a := a, n := Succ(n))))
    val powDefN = have((a ^ n) === app(G)(n)).by(Restate.from(pow.definition.of(a := a, n := n)))
    val powDefNSym = have(app(G)(n) === (a ^ n)).by(Congruence.from(powDefN))
    val rhsEq2 = have(app(G)(n) * a === (a ^ n) * a).by(Congruence.from(powDefNSym))

    val recSn = have(Succ(n) ∈ ℕ |- ((a ^ Succ(n)) === ((a ^ n) * a))).by(Congruence.from(powDefSn, eqSnr, rhsEq, rhsEq2))

    have(thesis).by(Cut(SnInℕ, recSn))
  }

  /** Theorem: closure of exponentiation on naturals. */
  val powClosed = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ n) ∈ ℕ)) {
    val aInℕ = assume(a ∈ ℕ)

    val P = λ(n, (a ^ n) ∈ ℕ)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
      val iff = have((a ^ 0) ∈ ℕ <=> 1 ∈ ℕ).by(Congruence.from(eq0))
      have((a ^ 0) ∈ ℕ).by(Tautology.from(iff, Nat.oneInℕ))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := a, n := n)))
        val rhsInℕ = have(((a ^ n) * a) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := (a ^ n), n := a), IH, aInℕ))
        val iff = have((a ^ Succ(n)) ∈ ℕ <=> (((a ^ n) * a) ∈ ℕ)).by(Congruence.from(eq))
        have(P(Succ(n))).by(Tautology.from(iff, rhsInℕ))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Lemma: if `a ≠ 0` then `a^n ≠ 0` for naturals `n` (Isabelle/HOL: `power_eq_0_iff`, specialized). */
  val powNeZero = Theorem((a ∈ ℕ, a =/= 0, n ∈ ℕ) |- ((a ^ n) =/= 0)) {
    val aInℕ = assume(a ∈ ℕ)
    val aNe0 = assume(a =/= 0)

    val P = λ(n, (a ^ n) =/= 0)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
      val oneNe0 = have(1 =/= 0).by(Tautology.from(Nat.zeroInℕ, Nat.succNeZero.of(n := 0)))

      have((a ^ 0) === 0 |- ()) subproof {
        assume((a ^ 0) === 0)
        val oneEq0 = have(1 === 0).by(Congruence.from(eq0, lastStep))
        have(thesis).by(Tautology.from(oneEq0, oneNe0))
      }
      thenHave((a ^ 0) =/= 0).by(Restate)
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := a, n := n)))

        val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
        val iff = have((((a ^ n) * a) =/= 0) <=> (((a ^ n) =/= 0) /\ (a =/= 0))).by(
          Tautology.from(NatAlgebra.mulNeZeroIff.of(m := a ^ n, n := a), anInℕ, aInℕ)
        )
        val conj = have(((a ^ n) =/= 0) /\ (a =/= 0)).by(Tautology.from(IH, aNe0))
        val prodNe0 = have(((a ^ n) * a) =/= 0).by(Tautology.from(iff, conj))
        have((a ^ Succ(n)) =/= 0).by(Congruence.from(eq, prodNe0))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Lemma: `1^n = 1` for naturals `n` (Isabelle/HOL: `power_one`). */
  val powOneBase = Theorem(n ∈ ℕ |- ((1 ^ n) === 1)) {
    val P = λ(n, (1 ^ n) === 1)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)).by(Restate.from(powZero.of(a := 1)))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val onePowInℕ = have((1 ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := 1, n := n), Nat.oneInℕ, nInℕ))

        val eq = have((1 ^ Succ(n)) === ((1 ^ n) * 1)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := 1, n := n)))
        val mul1 = have((1 ^ n) * 1 === (1 ^ n)).by(Cut(onePowInℕ, NatAlgebra.mulOneRight.of(m := 1 ^ n)))
        val rhs = have((1 ^ n) * 1 === 1).by(Congruence.from(mul1, IH))
        val res = have((1 ^ Succ(n)) === 1).by(Congruence.from(eq, rhs))
        have(P(Succ(n))).by(Restate.from(res))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Lemma: `a^1 = a`. */
  val powOneRight = Theorem(a ∈ ℕ |- ((a ^ 1) === a)) {
    val aInℕ = assume(a ∈ ℕ)

    val eq = have((a ^ 1) === ((a ^ 0) * a)).by(Tautology.from(Nat.zeroInℕ, powSucc.of(a := a, n := 0)))
    val eq0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
    val rhs = have((a ^ 0) * a === a).by(Congruence.from(eq0, NatAlgebra.mulOneLeft.of(n := a)))

    have(thesis).by(Congruence.from(eq, rhs))
  }

  /** Lemma: `a^2 = a*a`. */
  val powTwo = Theorem(a ∈ ℕ |- ((a ^ 2) === (a * a))) {
    val aInℕ = assume(a ∈ ℕ)

    val eq = have((a ^ 2) === ((a ^ 1) * a)).by(Tautology.from(Nat.oneInℕ, powSucc.of(a := a, n := 1)))
    val eq1 = have((a ^ 1) === a).by(Cut(aInℕ, powOneRight.of(a := a)))
    have(thesis).by(Congruence.from(eq, eq1))
  }

  /** Lemma: `a^(Succ(n)) = a * a^n` (by commutativity). */
  val powSuccLeft = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ Succ(n)) === (a * (a ^ n)))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val eq = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := a, n := n)))
    val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
    val comm = have((a ^ n) * a === a * (a ^ n)).by(Tautology.from(NatAlgebra.mulComm.of(m := a ^ n, n := a), anInℕ, aInℕ))

    have(thesis).by(Congruence.from(eq, comm))
  }

  /** Lemma: `a^(n + 1) = a^n * a` for naturals `n` (Isabelle/HOL: `power_Suc2`, specialized). */
  val powAddOneRight = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ (n + 1)) === ((a ^ n) * a))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val nPlus1 = have(n + 1 === Succ(n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.addOneRight.of(n := n)))
    val eq = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := a, n := n)))

    val iff = have((a ^ (n + 1)) === (a ^ Succ(n))).by(Congruence.from(nPlus1))
    have(thesis).by(Congruence.from(iff, eq))
  }

  /** Theorem: `a^(m + n) = a^m * a^n`. */
  val powAdd = Theorem((a ∈ ℕ, m ∈ ℕ, n ∈ ℕ) |- ((a ^ (m + n)) === ((a ^ m) * (a ^ n)))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val P = λ(m, (a ^ (m + n)) === ((a ^ m) * (a ^ n)))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq0 = have(0 + n === n).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.addZeroLeft.of(n := n)))
      val lhs = have((a ^ (0 + n)) === (a ^ n)).by(Congruence.from(eq0))

      val eqPow0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
      val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
      val mul1 = have((1 * (a ^ n)) === (a ^ n)).by(Tautology.from(NatAlgebra.mulOneLeft.of(n := a ^ n), anInℕ))
      val rhs = have(((a ^ 0) * (a ^ n)) === (a ^ n)).by(Congruence.from(eqPow0, mul1))

      val rhsSym = have((a ^ n) === ((a ^ 0) * (a ^ n))).by(Congruence.from(rhs))
      val goalEq = have((a ^ (0 + n)) === ((a ^ 0) * (a ^ n))).by(Congruence.from(lhs, rhsSym))
      have(thesis).by(Restate.from(goalEq))
    }

    val step = have(∀(m, (m ∈ ℕ) ==> (P(m) ==> P(Succ(m))))) subproof {
      have((m ∈ ℕ) ==> (P(m) ==> P(Succ(m)))) subproof {
        val mInℕ0 = assume(m ∈ ℕ)
        val IH = assume(P(m))

        val mnInℕ = have((m + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := n), mInℕ0, nInℕ))

        val amInℕ = have((a ^ m) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := m), aInℕ, mInℕ0))
        val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
        val amnInℕ = have((a ^ (m + n)) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := (m + n)), aInℕ, mnInℕ))

        val addSucc = have(Succ(m) + n === Succ(m + n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.addSuccLeft.of(m := m, n := n)))
        val lhs1 = have((a ^ (Succ(m) + n)) === (a ^ Succ(m + n))).by(Congruence.from(addSucc))

        val lhs2 = have((a ^ Succ(m + n)) === ((a ^ (m + n)) * a)).by(Cut(mnInℕ, powSucc.of(a := a, n := m + n)))

        val rhsPowSucc = have((a ^ Succ(m)) === ((a ^ m) * a)).by(Cut(have(m ∈ ℕ).by(Weakening(mInℕ0)), powSucc.of(a := a, n := m)))

        // (a^(m+n))*a = (a^m*a^n)*a  (by IH)
        val mid0 = have((a ^ (m + n)) * a === ((a ^ m) * (a ^ n)) * a).by(Congruence.from(IH))

        // ((a^m*a^n)*a) = (a^m*(a^n*a)) (assoc)
        val assoc1 = have(((a ^ m) * (a ^ n)) * a === (a ^ m) * ((a ^ n) * a)).by(
          Tautology.from(NatAlgebra.mulAssoc.of(a := a ^ m, b := a ^ n, c := a), amInℕ, anInℕ, aInℕ)
        )

        // (a^n*a) = (a*a^n) (comm)
        val comm1 = have((a ^ n) * a === a * (a ^ n)).by(Tautology.from(NatAlgebra.mulComm.of(m := a ^ n, n := a), anInℕ, aInℕ))

        // a^m * (a^n*a) = a^m * (a*a^n) (congruence)
        val cong1 = have((a ^ m) * ((a ^ n) * a) === (a ^ m) * (a * (a ^ n))).by(Congruence.from(comm1))

        // a^m * (a*a^n) = (a^m*a) * a^n (assoc backwards)
        val assoc2a = have(((a ^ m) * a) * (a ^ n) === (a ^ m) * (a * (a ^ n))).by(
          Tautology.from(NatAlgebra.mulAssoc.of(a := a ^ m, b := a, c := a ^ n), amInℕ, aInℕ, anInℕ)
        )
        val assoc2 = have((a ^ m) * (a * (a ^ n)) === ((a ^ m) * a) * (a ^ n)).by(Congruence.from(assoc2a))

        val chain = have(((a ^ m) * (a ^ n)) * a === ((a ^ m) * a) * (a ^ n)).by(Congruence.from(assoc1, cong1, assoc2))

        val rhsR = have(((a ^ m) * a) * (a ^ n) === (a ^ Succ(m)) * (a ^ n)).by(Congruence.from(rhsPowSucc))
        val rhsFinal = have(((a ^ m) * (a ^ n)) * a === (a ^ Succ(m)) * (a ^ n)).by(Congruence.from(chain, rhsR))

        val lhs3 = have((a ^ Succ(m + n)) === ((a ^ Succ(m)) * (a ^ n))).by(Congruence.from(lhs2, mid0, rhsFinal))

        val goalEq = have((a ^ (Succ(m) + n)) === ((a ^ Succ(m)) * (a ^ n))).by(Congruence.from(lhs1, lhs3))
        have(P(Succ(m))).by(Restate.from(goalEq))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(m, (m ∈ ℕ) ==> P(m))).by(Tautology.from(ind, base, step))

    val imp = have((m ∈ ℕ) ==> P(m)).by(InstantiateForall(m)(allP))
    val mInℕ = assume(m ∈ ℕ)
    val res = have(P(m)).by(Tautology.from(imp, mInℕ))

    have(thesis).by(Restate.from(res))
  }

  /** Theorem: `a^(m*n) = (a^m)^n` (Isabelle/HOL: `power_mult`). */
  val powMul = Theorem((a ∈ ℕ, m ∈ ℕ, n ∈ ℕ) |- ((a ^ (m * n)) === ((a ^ m) ^ n))) {
    val aInℕ = assume(a ∈ ℕ)
    val mInℕ = assume(m ∈ ℕ)

    val P = λ(n, (a ^ (m * n)) === ((a ^ m) ^ n))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq0 = have(m * 0 === 0).by(Cut(have(m ∈ ℕ).by(Weakening(mInℕ)), NatAlgebra.mulZeroRight.of(m := m)))
      val lhs = have((a ^ (m * 0)) === (a ^ 0)).by(Congruence.from(eq0))
      val rhs = have(((a ^ m) ^ 0) === 1).by(Restate.from(powZero.of(a := a ^ m)))
      val lhs0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))

      val lhs1 = have((a ^ (m * 0)) === 1).by(Congruence.from(lhs, lhs0))
      val rhsSym = have(1 === ((a ^ m) ^ 0)).by(Congruence.from(rhs))
      val goalEq = have((a ^ (m * 0)) === ((a ^ m) ^ 0)).by(Congruence.from(lhs1, rhsSym))
      have(thesis).by(Restate.from(goalEq))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ0 = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val mulSucc = have(m * Succ(n) === (m * n) + m).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ0)), NatAlgebra.mulSuccRight.of(m := m, n := n)))
        val lhs1 = have((a ^ (m * Succ(n))) === (a ^ ((m * n) + m))).by(Congruence.from(mulSucc))

        val mnInℕ = have((m * n) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := n), mInℕ, nInℕ0))
        val powAddInst = have((a ^ ((m * n) + m)) === ((a ^ (m * n)) * (a ^ m))).by(
          Tautology.from(powAdd.of(a := a, m := (m * n), n := m), aInℕ, mnInℕ, mInℕ)
        )

        val rhsPowAdd = have((a ^ (m * n)) === ((a ^ m) ^ n)).by(Restate.from(IH))
        val rhs2 = have((a ^ ((m * n) + m)) === (((a ^ m) ^ n) * (a ^ m))).by(Congruence.from(powAddInst, rhsPowAdd))

        val powSuccInst = have(((a ^ m) ^ Succ(n)) === (((a ^ m) ^ n) * (a ^ m))).by(Tautology.from(nInℕ0, powSucc.of(a := a ^ m, n := n)))
        val rhs3 = have((((a ^ m) ^ n) * (a ^ m)) === ((a ^ m) ^ Succ(n))).by(Congruence.from(powSuccInst))

        val trans = have(
          ((a ^ (m * Succ(n))) === (a ^ ((m * n) + m)), (a ^ ((m * n) + m)) === (((a ^ m) ^ n) * (a ^ m)), (((a ^ m) ^ n) * (a ^ m)) === ((a ^ m) ^ Succ(n))) |- (a ^ (m * Succ(n))) === ((a ^ m) ^ Succ(n))
        ).by(Congruence)

        val goalEq = have((a ^ (m * Succ(n))) === ((a ^ m) ^ Succ(n))).by(Tautology.from(trans, lhs1, rhs2, rhs3))
        have(P(Succ(n))).by(Restate.from(goalEq))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Theorem: `(a*b)^n = a^n * b^n` (Isabelle/HOL: `power_mult_distrib`, for naturals). */
  val powMulDistrib = Theorem((a ∈ ℕ, b ∈ ℕ, n ∈ ℕ) |- (((a * b) ^ n) === (a ^ n) * (b ^ n))) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)

    val abInℕ = have((a * b) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := a, n := b), aInℕ, bInℕ))

    val P = λ(n, ((a * b) ^ n) === (a ^ n) * (b ^ n))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val lhs = have(((a * b) ^ 0) === 1).by(Restate.from(powZero.of(a := (a * b))))

      val a0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
      val b0 = have((b ^ 0) === 1).by(Restate.from(powZero.of(a := b)))
      val a0Inℕ = have((a ^ 0) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := 0), aInℕ, Nat.zeroInℕ))
      val mul1 = have((a ^ 0) * 1 === (a ^ 0)).by(Cut(a0Inℕ, NatAlgebra.mulOneRight.of(m := a ^ 0)))
      val rhs0 = have((a ^ 0) * (b ^ 0) === (a ^ 0) * 1).by(Congruence.from(b0))
      val rhs1 = have((a ^ 0) * (b ^ 0) === (a ^ 0)).by(Congruence.from(rhs0, mul1))
      val rhs = have((a ^ 0) * (b ^ 0) === 1).by(Congruence.from(rhs1, a0))
      val rhsSym = have(1 === (a ^ 0) * (b ^ 0)).by(Congruence.from(rhs))

      val trans = have((((a * b) ^ 0) === 1, 1 === (a ^ 0) * (b ^ 0)) |- ((a * b) ^ 0) === (a ^ 0) * (b ^ 0)).by(Congruence)
      have(thesis).by(Tautology.from(trans, lhs, rhsSym))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
        val bnInℕ = have((b ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := b, n := n), bInℕ, nInℕ))
        val bnbInℕ = have(((b ^ n) * b) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := (b ^ n), n := b), bnInℕ, bInℕ))

        val lhs0 = have(((a * b) ^ Succ(n)) === (((a * b) ^ n) * (a * b))).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := (a * b), n := n)))
        val lhs1 = have((((a * b) ^ n) * (a * b)) === (((a ^ n) * (b ^ n)) * (a * b))).by(Congruence.from(IH))

        val assoc1 = have((((a ^ n) * (b ^ n)) * (a * b)) === ((a ^ n) * ((b ^ n) * (a * b)))).by(
          Tautology.from(NatAlgebra.mulAssoc.of(a := (a ^ n), b := (b ^ n), c := (a * b)), anInℕ, bnInℕ, abInℕ)
        )
        val leftComm = have(((b ^ n) * (a * b)) === (a * ((b ^ n) * b))).by(
          Tautology.from(NatAlgebra.mulLeftComm.of(a := (b ^ n), b := a, c := b), bnInℕ, aInℕ, bInℕ)
        )
        val cong1 = have((a ^ n) * ((b ^ n) * (a * b)) === (a ^ n) * (a * ((b ^ n) * b))).by(Congruence.from(leftComm))
        val mid = have((((a ^ n) * (b ^ n)) * (a * b)) === (a ^ n) * (a * ((b ^ n) * b))).by(Congruence.from(assoc1, cong1))

        val assoc2 = have(((a ^ n) * a) * ((b ^ n) * b) === (a ^ n) * (a * ((b ^ n) * b))).by(
          Tautology.from(NatAlgebra.mulAssoc.of(a := (a ^ n), b := a, c := ((b ^ n) * b)), anInℕ, aInℕ, bnbInℕ)
        )
        val assoc2sym = have((a ^ n) * (a * ((b ^ n) * b)) === ((a ^ n) * a) * ((b ^ n) * b)).by(Congruence.from(assoc2))

        val aPow = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := a, n := n)))
        val bPow = have((b ^ Succ(n)) === ((b ^ n) * b)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := b, n := n)))
        val aPowSym = have(((a ^ n) * a) === (a ^ Succ(n))).by(Congruence.from(aPow))
        val bPowSym = have(((b ^ n) * b) === (b ^ Succ(n))).by(Congruence.from(bPow))
        val rhs = have((((a ^ n) * a) * ((b ^ n) * b)) === ((a ^ Succ(n)) * (b ^ Succ(n)))).by(Congruence.from(aPowSym, bPowSym))

        val lhs2 = have(((a * b) ^ Succ(n)) === (a ^ n) * (a * ((b ^ n) * b))).by(Congruence.from(lhs0, lhs1, mid))
        val goalEq = have(((a * b) ^ Succ(n)) === (a ^ Succ(n)) * (b ^ Succ(n))).by(Congruence.from(lhs2, assoc2sym, rhs))
        have(P(Succ(n))).by(Restate.from(goalEq))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Lemma: `0^(Succ(n)) = 0` for naturals `n`. */
  val zeroPowSucc = Theorem(n ∈ ℕ |- ((0 ^ Succ(n)) === 0)) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have((0 ^ Succ(n)) === ((0 ^ n) * 0)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := 0, n := n)))
    val zeroPowInℕ = have((0 ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := 0, n := n), Nat.zeroInℕ, nInℕ))
    val rhs = have((0 ^ n) * 0 === 0).by(Cut(zeroPowInℕ, NatAlgebra.mulZeroRight.of(m := 0 ^ n)))
    have(thesis).by(Congruence.from(eq, rhs))
  }

  /** Lemma: `0^n = (if n = 0 then 1 else 0)` as a disjunction form. */
  val zeroPowCases = Theorem(n ∈ ℕ |- ((n === 0) \/ ((0 ^ n) === 0))) {
    val P = λ(n, (n === 0) \/ ((0 ^ n) === 0))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val zRefl = have(0 === 0).by(Restate)
      have(thesis).by(Tautology.from(zRefl))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ0 = assume(n ∈ ℕ)
        assume(P(n))

        val pow0 = have((0 ^ Succ(n)) === 0).by(Tautology.from(zeroPowSucc.of(n := n), nInℕ0))
        have(thesis).by(Tautology.from(pow0))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Theorem: `a^(Succ(n)) = 0 <=> a = 0` (for naturals). */
  val powEqZeroSuccIff = Theorem((a ∈ ℕ, n ∈ ℕ) |- (((a ^ Succ(n)) === 0) <=> (a === 0))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val SnInℕ = have(Succ(n) ∈ ℕ).by(Cut(nInℕ, Nat.succClosed.of(n := n)))

    val `==>` = have((a ^ Succ(n)) === 0 |- a === 0) subproof {
      val eq0 = assume((a ^ Succ(n)) === 0)

      val em = have((a === 0) \/ (a =/= 0)).by(Tautology)

      val case0 = have(a === 0 |- a === 0).by(Tautology)
      val case0Imp = have((a === 0) ==> (a === 0)).by(Restate.from(case0))

      val caseNe0 = have(a =/= 0 |- a === 0) subproof {
        val aNe0 = assume(a =/= 0)
        val powNe0 = have((a ^ Succ(n)) =/= 0).by(Tautology.from(powNeZero.of(a := a, n := Succ(n)), aInℕ, aNe0, SnInℕ))
        val contra = have(a =/= 0 |- ()).by(Tautology.from(eq0, powNe0))
        have(thesis).by(Weakening(contra))
      }
      val caseNe0Imp = have((a =/= 0) ==> (a === 0)).by(Restate.from(caseNe0))

      have(thesis).by(Tautology.from(em, case0Imp, caseNe0Imp))
    }

    val `<==` = have(a === 0 |- (a ^ Succ(n)) === 0) subproof {
      val aEq0 = assume(a === 0)
      val eqPow = have((a ^ Succ(n)) === (0 ^ Succ(n))).by(Congruence.from(aEq0))
      val zPow = have((0 ^ Succ(n)) === 0).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), zeroPowSucc.of(n := n)))
      have(thesis).by(Congruence.from(eqPow, zPow))
    }

    have(thesis).by(Tautology.from(`==>`, `<==`))
  }

  /** Theorem: if `Even(a)` then `Even(a^(Succ(n)))`. */
  val evenPowSucc = Theorem((a ∈ ℕ, n ∈ ℕ, NatParity.Even(a)) |- NatParity.Even(a ^ Succ(n))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val evenA = assume(NatParity.Even(a))

    val eq = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), powSucc.of(a := a, n := n)))

    val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))

    val evenProd = have(NatParity.Even((a ^ n) * a)).by(Tautology.from(NatParity.evenMulRight.of(m := a ^ n, n := a), anInℕ, aInℕ, evenA))

    val iff = have(NatParity.Even(a ^ Succ(n)) <=> NatParity.Even((a ^ n) * a)).by(Congruence.from(eq))
    have(thesis).by(Tautology.from(iff, evenProd))
  }

  /** Theorem: if `Odd(a)` then `Odd(a^n)` for naturals `n`. */
  val oddPow = Theorem((a ∈ ℕ, n ∈ ℕ, NatParity.Odd(a)) |- NatParity.Odd(a ^ n)) {
    val aInℕ = assume(a ∈ ℕ)
    val oddA = assume(NatParity.Odd(a))

    val P = λ(n, NatParity.Odd(a ^ n))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
      val iff = have(NatParity.Odd(a ^ 0) <=> NatParity.Odd(1)).by(Congruence.from(eq0))
      have(NatParity.Odd(a ^ 0)).by(Tautology.from(iff, NatParity.oddOne))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ0 = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq = have((a ^ Succ(n)) === ((a ^ n) * a)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ0)), powSucc.of(a := a, n := n)))

        val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ0))

        val oddProd = have(NatParity.Odd((a ^ n) * a)).by(Tautology.from(NatParity.oddMulOdd.of(m := a ^ n, n := a), anInℕ, aInℕ, IH, oddA))

        val iff = have(NatParity.Odd(a ^ Succ(n)) <=> NatParity.Odd((a ^ n) * a)).by(Congruence.from(eq))
        have(P(Succ(n))).by(Tautology.from(iff, oddProd))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))

    have(thesis).by(Restate.from(res))
  }

  /** Corollary: if `Odd(a)` then `Odd(a^(Succ(n)))`. */
  val oddPowSucc = Theorem((a ∈ ℕ, n ∈ ℕ, NatParity.Odd(a)) |- NatParity.Odd(a ^ Succ(n))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val oddA = assume(NatParity.Odd(a))
    val SnInℕ = have(Succ(n) ∈ ℕ).by(Tautology.from(Nat.succClosed.of(n := n), nInℕ))
    have(thesis).by(Tautology.from(oddPow.of(a := a, n := Succ(n)), aInℕ, SnInℕ, oddA))
  }

  // -------------------------
  // Extra power algebra lemmas (Power.thy-inspired)
  // -------------------------

  /** Lemma: `a^n * a = a * a^n` for naturals (commutativity). */
  val powCommutesRight = Theorem((a ∈ ℕ, n ∈ ℕ) |- (((a ^ n) * a) === (a * (a ^ n)))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
    have(thesis).by(Tautology.from(NatAlgebra.mulComm.of(m := (a ^ n), n := a), anInℕ, aInℕ))
  }

  /** Lemma: `a^(n+0) = a^n` for naturals. */
  val powAddZeroRight = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ (n + 0)) === (a ^ n))) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have(n + 0 === n).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.addZeroRight.of(m := n)))
    have(thesis).by(Congruence.from(eq))
  }

  /** Lemma: `a^(0+n) = a^n` for naturals. */
  val powAddZeroLeft = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ (0 + n)) === (a ^ n))) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have(0 + n === n).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.addZeroLeft.of(n := n)))
    have(thesis).by(Congruence.from(eq))
  }

  /** Lemma: `a^(n*0) = 1` for naturals. */
  val powMulZeroRight = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ (n * 0)) === 1)) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have(n * 0 === 0).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.mulZeroRight.of(m := n)))
    val lhs = have((a ^ (n * 0)) === (a ^ 0)).by(Congruence.from(eq))
    val rhs = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
    have(thesis).by(Congruence.from(lhs, rhs))
  }

  /** Lemma: `a^(n*1) = a^n` for naturals. */
  val powMulOneRight = Theorem((a ∈ ℕ, n ∈ ℕ) |- ((a ^ (n * 1)) === (a ^ n))) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have(n * 1 === n).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatAlgebra.mulOneRight.of(m := n)))
    have(thesis).by(Congruence.from(eq))
  }

  /** Lemma: `0^0 = 1`. */
  val zeroPowZero = Theorem(pow(0)(0) === 1) {
    have(thesis).by(Restate.from(powZero.of(a := 0)))
  }

  /** Lemma: `n∈ℕ ∧ n≠0 ⟹ 0^n = 0`. */
  val zeroPowNeZeroExp = Theorem((n ∈ ℕ, n =/= 0) |- ((0 ^ n) === 0)) {
    val nInℕ = assume(n ∈ ℕ)
    val nNe0 = assume(n =/= 0)

    val cases = have((n === 0) \/ ((0 ^ n) === 0)).by(Tautology.from(zeroPowCases.of(n := n), nInℕ))
    val notEq0 = have(¬(n === 0)).by(Tautology.from(nNe0))
    have(thesis).by(Tautology.from(cases, notEq0))
  }

  /** Theorem (Parity.thy `even_power`, nat-specialized): `Even(a^n) ⇔ (Even(a) ∧ n≠0)` for naturals. */
  val evenPowIff = Theorem((a ∈ ℕ, n ∈ ℕ) |- (NatParity.Even(a ^ n) <=> (NatParity.Even(a) /\ (n =/= 0)))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    // -> direction
    val forward = have(NatParity.Even(a ^ n) |- (NatParity.Even(a) /\ (n =/= 0))) subproof {
      val evenPow = assume(NatParity.Even(a ^ n))

      // n ≠ 0 (otherwise a^0 = 1 is not even)
      have(n === 0 |- ()) subproof {
        val nEq0 = assume(n === 0)
        val powEq = have((a ^ n) === (a ^ 0)).by(Congruence.from(nEq0))
        val a0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
        val powEq1 = have((a ^ n) === 1).by(Congruence.from(powEq, a0))
        val even1 = have(NatParity.Even(1)).by(Congruence.from(powEq1, evenPow))
        have(thesis).by(Tautology.from(even1, NatParity.notEvenOne))
      }
      val nNe0 = thenHave(n =/= 0).by(Restate)

      // Even(a): rule out Odd(a) via oddPow + disjointness
      val splitA = have(NatParity.Even(a) \/ NatParity.Odd(a)).by(Tautology.from(NatParity.parityExhaustive.of(n := a), aInℕ))

      val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
      val disjPow = have(¬(NatParity.Even(a ^ n) /\ NatParity.Odd(a ^ n))).by(Tautology.from(NatParity.evenOddDisjoint.of(n := (a ^ n)), anInℕ))

      val caseEvenA = have(NatParity.Even(a) |- NatParity.Even(a)).by(Tautology)

      val caseOddA = have(NatParity.Odd(a) |- NatParity.Even(a)) subproof {
        val oddA = assume(NatParity.Odd(a))
        val oddPowAn = have(NatParity.Odd(a ^ n)).by(Tautology.from(oddPow.of(a := a, n := n), aInℕ, nInℕ, oddA))
        val both = have(NatParity.Even(a ^ n) /\ NatParity.Odd(a ^ n)).by(Tautology.from(evenPow, oddPowAn))
        val contra = have(NatParity.Odd(a) |- ()).by(Tautology.from(both, disjPow))
        have(thesis).by(Weakening(contra))
      }

      val evenA = have(NatParity.Even(a)).by(Tautology.from(splitA, caseEvenA, caseOddA))
      have(thesis).by(Tautology.from(evenA, nNe0))
    }

    // <- direction
    val backward = have((NatParity.Even(a) /\ (n =/= 0)) |- NatParity.Even(a ^ n)) subproof {
      val conj = assume(NatParity.Even(a) /\ (n =/= 0))
      val evenA = have(NatParity.Even(a)).by(Tautology.from(conj))
      val nNe0 = have(n =/= 0).by(Tautology.from(conj))
      val notEq0 = have(¬(n === 0)).by(Tautology.from(nNe0))

      val cases = have((n === 0) \/ ∃(m, (m ∈ ℕ) /\ (n === Succ(m)))).by(Tautology.from(Nat.natCases.of(n := n), nInℕ))
      val ex = have(∃(m, (m ∈ ℕ) /\ (n === Succ(m)))).by(Tautology.from(cases, notEq0))

      have(∃(m, (m ∈ ℕ) /\ (n === Succ(m))) |- NatParity.Even(a ^ n)) subproof {
        assume(∃(m, (m ∈ ℕ) /\ (n === Succ(m))))
        have((m ∈ ℕ) /\ (n === Succ(m)) |- NatParity.Even(a ^ n)) subproof {
          assume((m ∈ ℕ) /\ (n === Succ(m)))
          val mInℕ = have((m ∈ ℕ) /\ (n === Succ(m)) |- m ∈ ℕ).by(Tautology)
          val nEq = have((m ∈ ℕ) /\ (n === Succ(m)) |- n === Succ(m)).by(Tautology)
          val powEq = have((m ∈ ℕ) /\ (n === Succ(m)) |- (a ^ n) === (a ^ Succ(m))).by(Congruence.from(nEq))
          val evenSuccPow = have((m ∈ ℕ) /\ (n === Succ(m)) |- NatParity.Even(a ^ Succ(m))).by(
            Tautology.from(evenPowSucc.of(a := a, n := m), aInℕ, mInℕ, evenA)
          )
          have(thesis).by(Congruence.from(powEq, evenSuccPow))
        }
        thenHave(thesis).by(LeftExists)
      }

      have(thesis).by(Cut(ex, lastStep))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  /** Theorem: `Odd(a^n) ⇔ (n=0 ∨ Odd(a))` for naturals. */
  val oddPowIff = Theorem((a ∈ ℕ, n ∈ ℕ) |- (NatParity.Odd(a ^ n) <=> ((n === 0) \/ NatParity.Odd(a)))) {
    val aInℕ = assume(a ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    // -> direction
    val forward = have(NatParity.Odd(a ^ n) |- ((n === 0) \/ NatParity.Odd(a))) subproof {
      val oddPowN = assume(NatParity.Odd(a ^ n))

      val em = have((n === 0) \/ (n =/= 0)).by(Tautology)

      val caseEq0 = have(n === 0 |- (n === 0) \/ NatParity.Odd(a)).by(Tautology)
      val caseEq0Imp = have((n === 0) ==> ((n === 0) \/ NatParity.Odd(a))).by(Restate.from(caseEq0))

      val caseNe0 = have(n =/= 0 |- (n === 0) \/ NatParity.Odd(a)) subproof {
        val nNe0 = assume(n =/= 0)
        val notEq0 = have(¬(n === 0)).by(Tautology.from(nNe0))

        val splitA = have(NatParity.Even(a) \/ NatParity.Odd(a)).by(Tautology.from(NatParity.parityExhaustive.of(n := a), aInℕ))
        val caseOddA = have(NatParity.Odd(a) |- (n === 0) \/ NatParity.Odd(a)).by(Tautology)

        val caseEvenA = have(NatParity.Even(a) |- (n === 0) \/ NatParity.Odd(a)) subproof {
          val evenA = assume(NatParity.Even(a))
          val evenPow = have(NatParity.Even(a ^ n)).by(Tautology.from(evenPowIff.of(a := a, n := n), aInℕ, nInℕ, evenA, nNe0))
          val anInℕ = have((a ^ n) ∈ ℕ).by(Tautology.from(powClosed.of(a := a, n := n), aInℕ, nInℕ))
          val disj = have(¬(NatParity.Even(a ^ n) /\ NatParity.Odd(a ^ n))).by(Tautology.from(NatParity.evenOddDisjoint.of(n := (a ^ n)), anInℕ))
          val both = have(NatParity.Even(a ^ n) /\ NatParity.Odd(a ^ n)).by(Tautology.from(evenPow, oddPowN))
          val contra = have(NatParity.Even(a) |- ()).by(Tautology.from(both, disj))
          have(thesis).by(Weakening(contra))
        }

        val oddA = have(NatParity.Odd(a)).by(Tautology.from(splitA, caseEvenA, caseOddA))
        have(thesis).by(Tautology.from(oddA))
      }
      val caseNe0Imp = have((n =/= 0) ==> ((n === 0) \/ NatParity.Odd(a))).by(Restate.from(caseNe0))

      have(thesis).by(Tautology.from(em, caseEq0Imp, caseNe0Imp))
    }

    // <- direction
    val backward = have(((n === 0) \/ NatParity.Odd(a)) |- NatParity.Odd(a ^ n)) subproof {
      val split = assume((n === 0) \/ NatParity.Odd(a))

      val case0 = have(n === 0 |- NatParity.Odd(a ^ n)) subproof {
        val nEq0 = assume(n === 0)
        val powEq = have((a ^ n) === (a ^ 0)).by(Congruence.from(nEq0))
        val a0 = have((a ^ 0) === 1).by(Restate.from(powZero.of(a := a)))
        val powEq1 = have((a ^ n) === 1).by(Congruence.from(powEq, a0))
        have(thesis).by(Congruence.from(powEq1, NatParity.oddOne))
      }

      val caseOddA = have(NatParity.Odd(a) |- NatParity.Odd(a ^ n)).by(Tautology.from(oddPow.of(a := a, n := n), aInℕ, nInℕ))

      have(thesis).by(Tautology.from(split, case0, caseOddA))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  /** Lemma: `a∈ℕ ⟹ a^3 = (a*a)*a`. */
  val powThree = Theorem(a ∈ ℕ |- ((a ^ 3) === ((a * a) * a))) {
    val aInℕ = assume(a ∈ ℕ)

    val z = have(0 ∈ ℕ).by(Weakening(Nat.zeroInℕ))
    val o = have(1 ∈ ℕ).by(Cut(z, Nat.succClosed.of(n := 0)))
    val t = have(2 ∈ ℕ).by(Cut(o, Nat.succClosed.of(n := 1)))

    val eq = have((a ^ 3) === ((a ^ 2) * a)).by(Cut(t, powSucc.of(a := a, n := 2)))
    val eq2 = have((a ^ 2) === (a * a)).by(Cut(aInℕ, powTwo.of(a := a)))
    val rhs = have(((a ^ 2) * a) === ((a * a) * a)).by(Congruence.from(eq2))
    have(thesis).by(Congruence.from(eq, rhs))
  }

  /** Lemma: `a∈ℕ ⟹ a^4 = ((a*a)*a)*a`. */
  val powFour = Theorem(a ∈ ℕ |- ((a ^ 4) === (((a * a) * a) * a))) {
    val aInℕ = assume(a ∈ ℕ)

    val z = have(0 ∈ ℕ).by(Weakening(Nat.zeroInℕ))
    val o = have(1 ∈ ℕ).by(Cut(z, Nat.succClosed.of(n := 0)))
    val t = have(2 ∈ ℕ).by(Cut(o, Nat.succClosed.of(n := 1)))
    val th = have(3 ∈ ℕ).by(Cut(t, Nat.succClosed.of(n := 2)))

    val eq = have((a ^ 4) === ((a ^ 3) * a)).by(Cut(th, powSucc.of(a := a, n := 3)))
    val eq3 = have((a ^ 3) === ((a * a) * a)).by(Cut(aInℕ, powThree.of(a := a)))
    val rhs = have(((a ^ 3) * a) === (((a * a) * a) * a)).by(Congruence.from(eq3))
    have(thesis).by(Congruence.from(eq, rhs))
  }
}
