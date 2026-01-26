package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Order.WellOrders.{InitialSegment, WellOrder}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation

/**
 * Derived constructions over `Nat`.
 *
 * This file intentionally hosts lemmas/defs that are not part of the core `Nat` API.
 */
object NatDerived extends lisa.Main {
  private val nn = variable[Ind]
  private val m = variable[Ind]
  private val n = variable[Ind]
  private val k = variable[Ind]
  private val x = variable[Ind]
  private val h = variable[Ind]
  private val y = variable[Ind]

  // Local copy (structurally identical to Nat's) to avoid accessing Nat.memRel (which is private).
  private val memRel = MembershipRelation.membershipRelation(Nat.ℕ)

  /** Lemma: successor is never empty, hence `Succ(n) ≠ 0` (reproved here to avoid Nat's private lemma). */
  private val succNeZero = Lemma((n ∈ Nat.ℕ) |- (Nat.Succ(n) =/= Nat.zero)) {
    assume(n ∈ Nat.ℕ)
    val nInSn = have(n ∈ Nat.Succ(n)).by(Weakening(Nat.nInSucc.of(n := n)))
    have(Nat.Succ(n) === Nat.zero |- ()) subproof {
      assume(Nat.Succ(n) === Nat.zero)
      have(n ∈ Nat.zero) by Congruence.from(nInSn, lastStep)
      val nInEmpty = have(n ∈ ∅) by Congruence.from(Nat.zero.definition, lastStep)
      have(thesis) by Tautology.from(EmptySet.definition.of(x := n), nInEmpty)
    }
    thenHave(thesis) by Restate
  }

  /** Doubling (defined by well-ordered recursion on `(ℕ, ∈_ℕ)`). */
  val double = DEF(
    λ(nn,
      app(
        Necessary.recursiveFunctionOn(
          λ(
            x,
            λ(
              h,
              ε(
                y,
                ((x === Nat.zero) /\ (y === Nat.zero)) \/
                  ∃(k, (k ∈ Nat.ℕ) /\ (x === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(h)(k)))))
              )
            )
          )
        )(Nat.ℕ)(memRel)
      )(nn)
    )
  )

  /** Theorem: `double(0) = 0`. */
  val doubleZero = Theorem(double(Nat.zero) === Nat.zero) {
    val wo = have(WellOrder.wellOrder(Nat.ℕ)(memRel)).by(Restate.from(Nat.natWellOrder))

    val F = λ(
      x,
      λ(
        h,
        ε(
          y,
          ((x === Nat.zero) /\ (y === Nat.zero)) \/
            ∃(k, (k ∈ Nat.ℕ) /\ (x === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(h)(k)))))
        )
      )
    )

    val G = Necessary.recursiveFunctionOn(F)(Nat.ℕ)(memRel)

    val spec = have(
      functionOn(G)(Nat.ℕ) /\
        ∀(x ∈ Nat.ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(Nat.ℕ)(memRel)))
    ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := Nat.ℕ, R := memRel, Necessary.Func := F)))

    val eqAll = have(
      ∀(x ∈ Nat.ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(Nat.ℕ)(memRel)))
    ).by(Tautology.from(spec))

    val eq0 = have(
      Nat.zero ∈ Nat.ℕ |- app(G)(Nat.zero) === F(Nat.zero)(G ↾ InitialSegment.initialSegment(Nat.zero)(Nat.ℕ)(memRel))
    ).by(InstantiateForall(Nat.zero)(eqAll))

    val init0 = have(Nat.zero ∈ Nat.ℕ |- InitialSegment.initialSegment(Nat.zero)(Nat.ℕ)(memRel) === Nat.zero).by(
      Restate.from(Nat.natInitialSegment.of(n := Nat.zero))
    )

    val eq0r = have(Nat.zero ∈ Nat.ℕ |- app(G)(Nat.zero) === F(Nat.zero)(G ↾ Nat.zero)).by(Substitute(init0)(eq0))

    val Q = λ(
      y,
      ((Nat.zero === Nat.zero) /\ (y === Nat.zero)) \/
        ∃(k, (k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k)))))
    )

    val F0 = have(F(Nat.zero)(G ↾ Nat.zero) === ε(y, Q(y))).by(Restate)

    val exY = have(∃(y, Q(y))) subproof {
      val zRefl = have(Nat.zero === Nat.zero).by(Restate)
      val zRefl2 = have(Nat.zero === Nat.zero).by(Restate)
      have(Q(Nat.zero)).by(Tautology.from(zRefl, zRefl2))
      thenHave(thesis).by(RightExists)
    }

    val uniq = have(∀(y, Q(y) ==> (y === Nat.zero))) subproof {
      have(Q(y) |- y === Nat.zero) subproof {
        assume(Q(y))

        val case1 = have((Nat.zero === Nat.zero) /\ (y === Nat.zero) |- y === Nat.zero).by(Tautology)
        val case1Imp = have(((Nat.zero === Nat.zero) /\ (y === Nat.zero)) ==> (y === Nat.zero)).by(Restate.from(case1))

        val case2 = have(
          ∃(k, (k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k))))) |- y === Nat.zero
        ) subproof {
          val instK = have((k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k)))) |- ()) subproof {
            val conjK = assume((k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k)))))
            val kInℕ = have(k ∈ Nat.ℕ).by(Tautology.from(conjK))
            val zEqSk = have(Nat.zero === Nat.Succ(k)).by(Tautology.from(conjK))

            val SkEq0 = have(Nat.Succ(k) === Nat.zero).by(Congruence.from(zEqSk))
            val SkNe0 = have(Nat.Succ(k) =/= Nat.zero).by(Cut(kInℕ, succNeZero.of(n := k)))
            val notSkEq0 = have(¬(Nat.Succ(k) === Nat.zero)).by(Restate.from(SkNe0))
            have(thesis).by(Tautology.from(SkEq0, notSkEq0))
          }
          val exFalse = have(∃(k, (k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k))))) |- ()).by(
            LeftExists(instK)
          )
          have(thesis).by(Tautology.from(exFalse))
        }

        val case2Imp = have(
          ∃(k, (k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k))))) ==> (y === Nat.zero)
        ).by(Restate.from(case2))

        val disj = have(
          ((Nat.zero === Nat.zero) /\ (y === Nat.zero)) \/
            ∃(k, (k ∈ Nat.ℕ) /\ (Nat.zero === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(G ↾ Nat.zero)(k)))))
        ).by(Restate)

        have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
      }
      thenHave(Q(y) ==> (y === Nat.zero)).by(Restate)
      thenHave(thesis).by(RightForall)
    }

    val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

    val epsEq = have(ε(y, Q(y)) === Nat.zero) subproof {
      have(∀(y, Q(y) ==> (y === Nat.zero))).by(Restate.from(uniq))
      thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === Nat.zero)).by(InstantiateForall(ε(y, Q(y))))
      have(thesis).by(Tautology.from(epsQ, lastStep))
    }

    val doubleDef0 = have(double(Nat.zero) === app(G)(Nat.zero)).by(Restate.from(double.definition.of(nn := Nat.zero)))
    val rhsEq0 = have(F(Nat.zero)(G ↾ Nat.zero) === Nat.zero).by(Congruence.from(F0, epsEq))
    val rec0 = have(Nat.zero ∈ Nat.ℕ |- double(Nat.zero) === Nat.zero).by(Congruence.from(doubleDef0, eq0r, rhsEq0))
    have(thesis).by(Cut(Nat.zeroInℕ, rec0))
  }

  /** Theorem: `n ∈ ℕ ⇒ double(Succ(n)) = Succ(Succ(double(n)))`. */
  val doubleSucc = Theorem(n ∈ Nat.ℕ |- (double(Nat.Succ(n)) === Nat.Succ(Nat.Succ(double(n))))) {
    val nInℕ = assume(n ∈ Nat.ℕ)

      val wo = have(WellOrder.wellOrder(Nat.ℕ)(memRel)).by(Restate.from(Nat.natWellOrder))

      val F = λ(
        x,
        λ(
          h,
          ε(
            y,
            ((x === Nat.zero) /\ (y === Nat.zero)) \/
              ∃(k, (k ∈ Nat.ℕ) /\ (x === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(h)(k)))))
          )
        )
      )

      val G = Necessary.recursiveFunctionOn(F)(Nat.ℕ)(memRel)

      val spec = have(
        functionOn(G)(Nat.ℕ) /\
          ∀(x ∈ Nat.ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(Nat.ℕ)(memRel)))
      ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := Nat.ℕ, R := memRel, Necessary.Func := F)))

      val GOn = have(functionOn(G)(Nat.ℕ)).by(Tautology.from(spec))
      val eqAll = have(
        ∀(x ∈ Nat.ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(Nat.ℕ)(memRel)))
      ).by(Tautology.from(spec))

      val SnInℕ = have(Nat.Succ(n) ∈ Nat.ℕ).by(Cut(nInℕ, Nat.succClosed.of(n := n)))
      val eqSn = have(
        Nat.Succ(n) ∈ Nat.ℕ |- app(G)(Nat.Succ(n)) === F(Nat.Succ(n))(G ↾ InitialSegment.initialSegment(Nat.Succ(n))(Nat.ℕ)(memRel))
      ).by(InstantiateForall(Nat.Succ(n))(eqAll))

      val initSn = have(Nat.Succ(n) ∈ Nat.ℕ |- InitialSegment.initialSegment(Nat.Succ(n))(Nat.ℕ)(memRel) === Nat.Succ(n)).by(
        Restate.from(Nat.natInitialSegment.of(n := Nat.Succ(n)))
      )

      val eqSnr = have(Nat.Succ(n) ∈ Nat.ℕ |- app(G)(Nat.Succ(n)) === F(Nat.Succ(n))(G ↾ Nat.Succ(n))).by(Substitute(initSn)(eqSn))

      val hSn = G ↾ Nat.Succ(n)

      val Q = λ(
        y,
        ((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero)) \/
          ∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))))
      )

      val FSn = have(F(Nat.Succ(n))(hSn) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        val SnEqSn = have(Nat.Succ(n) === Nat.Succ(n)).by(Restate)
        val zRefl = have(Nat.Succ(Nat.Succ(app(hSn)(n))) === Nat.Succ(Nat.Succ(app(hSn)(n)))).by(Restate)
        have((n ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(n)) /\ (Nat.Succ(Nat.Succ(app(hSn)(n))) === Nat.Succ(Nat.Succ(app(hSn)(n))))).by(
          Tautology.from(nInℕ, SnEqSn, zRefl)
        )
        thenHave(
          ∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (Nat.Succ(Nat.Succ(app(hSn)(n))) === Nat.Succ(Nat.Succ(app(hSn)(k)))))
        ).by(RightExists)
        thenHave(Q(Nat.Succ(Nat.Succ(app(hSn)(n))))).by(Tautology)
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === Nat.Succ(Nat.Succ(app(hSn)(n)))))) subproof {
        have(Q(y) |- y === Nat.Succ(Nat.Succ(app(hSn)(n)))) subproof {
          assume(Q(y))

          val SnNe0 = have(Nat.Succ(n) =/= Nat.zero).by(Tautology.from(nInℕ, succNeZero.of(n := n)))
          val notSnEq0 = have(¬(Nat.Succ(n) === Nat.zero)).by(Tautology.from(SnNe0))

          val case1 = have((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero) |- y === Nat.Succ(Nat.Succ(app(hSn)(n)))) subproof {
            val SnEq0 = have((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero) |- Nat.Succ(n) === Nat.zero).by(Tautology)
            val notSnEq0Under = have((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero) |- ¬(Nat.Succ(n) === Nat.zero)).by(Weakening(notSnEq0))
            val contra = have((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero) |- ()).by(Tautology.from(SnEq0, notSnEq0Under))
            have(thesis).by(Weakening(contra))
          }
          val case1Imp = have(((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero)) ==> (y === Nat.Succ(Nat.Succ(app(hSn)(n))))).by(Restate.from(case1))

          val case2 = have(
            ∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k))))) |- y === Nat.Succ(Nat.Succ(app(hSn)(n)))
          ) subproof {
            assume(∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k))))))

            have((k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- y === Nat.Succ(Nat.Succ(app(hSn)(n)))) subproof {
              val SnEqSk = have((k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- Nat.Succ(n) === Nat.Succ(k)).by(Tautology)
              val yEq = have((k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- y === Nat.Succ(Nat.Succ(app(hSn)(k)))).by(Tautology)

              val inj = have(Nat.Succ(n) === Nat.Succ(k) |- n === k).by(Tautology.from(Nat.succInjective.of(m := n, n := k)))

              val nEqk = have((k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- n === k).by(Cut(SnEqSk, inj))
              val kEqn = have((k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- k === n).by(Congruence.from(nEqk))

              val hkEq = have((k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- app(hSn)(k) === app(hSn)(n)).by(
                Congruence.from(kEqn)
              )

              val SShkEq = have(
                (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))) |- Nat.Succ(Nat.Succ(app(hSn)(k))) === Nat.Succ(Nat.Succ(app(hSn)(n)))
              ).by(Congruence.from(hkEq))

              have(thesis).by(Congruence.from(yEq, SShkEq))
            }
            thenHave(
              ∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k))))) |- y === Nat.Succ(Nat.Succ(app(hSn)(n)))
            ).by(LeftExists)
          }

          val case2Imp = have(
            ∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k))))) ==> (y === Nat.Succ(Nat.Succ(app(hSn)(n))))
          ).by(Restate.from(case2))

          val disj = have(
            ((Nat.Succ(n) === Nat.zero) /\ (y === Nat.zero)) \/
              ∃(k, (k ∈ Nat.ℕ) /\ (Nat.Succ(n) === Nat.Succ(k)) /\ (y === Nat.Succ(Nat.Succ(app(hSn)(k)))))
          ).by(Restate)

          have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
        }
        thenHave(Q(y) ==> (y === Nat.Succ(Nat.Succ(app(hSn)(n))))).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

      val epsEq = have(ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(hSn)(n)))) subproof {
        have(∀(y, Q(y) ==> (y === Nat.Succ(Nat.Succ(app(hSn)(n)))))).by(Restate.from(uniq))
        thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(hSn)(n))))).by(InstantiateForall(ε(y, Q(y))))
        have(thesis).by(Tautology.from(epsQ, lastStep))
      }

      val hSnAtN = have(app(hSn)(n) === app(G)(n)) subproof {
        val SnSubℕ = have(Nat.Succ(n) ⊆ Nat.ℕ).by(Cut(SnInℕ, Nat.`n ∈ ℕ -> n ⊆ ℕ`.of(n := Nat.Succ(n))))
        val nInSn = have(n ∈ Nat.Succ(n)).by(Weakening(Nat.nInSucc.of(n := n)))
        val restEq = have((functionOn(G)(Nat.ℕ), Nat.Succ(n) ⊆ Nat.ℕ, n ∈ Nat.Succ(n)) |- app(G ↾ Nat.Succ(n))(n) === app(G)(n)).by(
          Restate.from(Necessary.restrictionAppSubset.of(f := G, A := Nat.ℕ, B := Nat.Succ(n), x := n))
        )
        have(thesis).by(Tautology.from(restEq, GOn, SnSubℕ, nInSn))
      }

      val rhsEq2 = have(Nat.Succ(Nat.Succ(app(hSn)(n))) === Nat.Succ(Nat.Succ(app(G)(n)))).by(Congruence.from(hSnAtN))
      val trans = have((ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(hSn)(n))), Nat.Succ(Nat.Succ(app(hSn)(n))) === Nat.Succ(Nat.Succ(app(G)(n)))) |- ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(G)(n)))).by(
        Congruence
      )
      val trans1 = have((ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(hSn)(n)))) |- ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(G)(n)))).by(Cut(rhsEq2, trans))
      val rhsEqEps = have(ε(y, Q(y)) === Nat.Succ(Nat.Succ(app(G)(n)))).by(Cut(epsEq, trans1))
      val rhsEq = have(F(Nat.Succ(n))(hSn) === Nat.Succ(Nat.Succ(app(G)(n)))).by(Restate.from(rhsEqEps))

      val doubleDefSn = have(double(Nat.Succ(n)) === app(G)(Nat.Succ(n))).by(Restate.from(double.definition.of(nn := Nat.Succ(n))))
      val doubleDefN = have(double(n) === app(G)(n)).by(Restate.from(double.definition.of(nn := n)))
      val SSdn = have(Nat.Succ(Nat.Succ(double(n))) === Nat.Succ(Nat.Succ(app(G)(n)))).by(Congruence.from(doubleDefN))

      val recSn = have(Nat.Succ(n) ∈ Nat.ℕ |- double(Nat.Succ(n)) === Nat.Succ(Nat.Succ(double(n)))).by(Congruence.from(doubleDefSn, eqSnr, rhsEq, SSdn))
      val res = have(double(Nat.Succ(n)) === Nat.Succ(Nat.Succ(double(n)))).by(Cut(SnInℕ, recSn))
      have(thesis).by(Restate.from(res))
  }
}
