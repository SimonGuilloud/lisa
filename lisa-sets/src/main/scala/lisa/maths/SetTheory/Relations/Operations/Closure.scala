package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations.Predef._
import lisa.maths.Quantifiers
import lisa.maths.Quantifiers.∃!

import Examples.IdentityRelation
import Examples.IdentityRelation.Δ

/**
 * The closure of a relation `R` with regards to a property `P` is the smallest
 * relation `Q ⊇ R` that has property `P`.
 *
 * Some closures have a closed form: for example, the
 * [[Closure.reflexiveClosure]] of `R` is `R ∪ Δ(R)`.
 */
object Closure extends lisa.Main {

  private val x, y = variable[Ind]
  private val X = variable[Ind]
  private val R, Q, Q_, S = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /**
   * Definition --- The closure of `R` with regards to `P` is the smallest relation
   * `Q ⊇ R` that has property `P`.
   */
  val closure = DEF(λ(R, λ(P, ε(Q, R ⊆ Q /\ P(Q) /\ (∀(x, P(x) /\ (R ⊆ x) ==> Q ⊆ x))))))

  /**
   * Reflexive closure --- The reflexive closure of a relation `R` on `X` is
   * the smallest reflexive relation on `X` containing `R`, i.e.,
   * `reflexiveClosure(R, X) = R ∪ Δ(X)`.
   */
  val reflexiveClosure = DEF(λ(R, λ(X, R ∪ Δ(X))))

  /**
   * Theorem --- The reflexive closure of any relation `R` is reflexive.
   */
  val reflexiveClosureIsReflexive = Theorem(
    reflexive(reflexiveClosure(R)(X))(X)
  ) {
    have(Δ(X) ⊆ (R ∪ Δ(X))) by Tautology.from(Union.rightSubset of (x := R, y := Δ(X)))
    thenHave(Δ(X) ⊆ reflexiveClosure(R)(X)) by Substitute(reflexiveClosure.definition)
    thenHave(thesis) by Tautology.fromLastStep(IdentityRelation.subset of (R := reflexiveClosure(R)(X)))
  }

  /**
   * Theorem --- The [[reflexiveClosure]] of `R` as defined above is indeed the
   * smallest reflexive relation containing `R`.
   *
   * Proof sketch:
   *   Let φ(Q) = R ⊆ Q ∧ reflexive(Q)(X) ∧ ∀(Q', reflexive(Q')(X) ∧ R ⊆ Q' ⇒ Q ⊆ Q').
   *   The closure is ε(Q, φ(Q)) by definition of `closure`.
   *   We show R ∪ Δ(X) satisfies φ:
   *     - R ⊆ R ∪ Δ(X) by union-left-subset
   *     - reflexive(R ∪ Δ(X))(X) by reflexiveClosureIsReflexive
   *     - For any Q' with reflexive(Q')(X) and R ⊆ Q':
   *         Δ(X) ⊆ Q' (by IdentityRelation.subset)
   *         R ∪ Δ(X) ⊆ Q' (by leftUnionSubset)
   *   We show φ has a unique witness:
   *     If φ(Q) and φ(Q'), then Q ⊆ Q' (Q is minimal for Q') and Q' ⊆ Q.
   *   So ∃!(Q, φ(Q)), and since φ(R ∪ Δ(X)), we get R ∪ Δ(X) = ε(Q, φ(Q)).
   */
  val reflexiveClosureValid = Theorem(
    reflexiveClosure(R)(X) === closure(R)(λ(R, reflexive(R)(X)))
  ) {
    // The closure predicate: φ(Q) = R ⊆ Q ∧ reflexive(Q)(X) ∧ ∀(x, reflexive(x)(X) ∧ R ⊆ x ⇒ Q ⊆ x)
    // Use `x` (not `Q_`) as bound variable to avoid alpha-capture with free `Q`

    // Step 1: R ∪ Δ(X) satisfies the closure predicate
    val satisfies = have(R ⊆ (R ∪ Δ(X)) /\ reflexive(R ∪ Δ(X))(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> ((R ∪ Δ(X)) ⊆ x))) subproof {
      val rSubset = have(R ⊆ (R ∪ Δ(X))) by Tautology.from(Union.leftSubset of (x := R, y := Δ(X)))
      val reflex = have(reflexive(R ∪ Δ(X))(X)) subproof {
        val rcIsReflex = have(reflexive(reflexiveClosure(R)(X))(X)) by Restate.from(reflexiveClosureIsReflexive)
        have(thesis) by Congruence.from(rcIsReflex, reflexiveClosure.definition of (R := R, X := X))
      }
      val minimal = have(∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> ((R ∪ Δ(X)) ⊆ x))) subproof {
        val deltaSubQ = have((reflexive(x)(X), R ⊆ x) |- Δ(X) ⊆ x) by Tautology.from(
          IdentityRelation.subset of (R := x)
        )
        have((reflexive(x)(X), R ⊆ x) |- (R ∪ Δ(X)) ⊆ x) by Tautology.from(
          deltaSubQ,
          Union.leftUnionSubset of (x := R, y := Δ(X), z := x)
        )
        thenHave(reflexive(x)(X) /\ (R ⊆ x) ==> ((R ∪ Δ(X)) ⊆ x)) by Restate
        thenHave(thesis) by RightForall
      }
      have(thesis) by Tautology.from(rSubset, reflex, minimal)
    }

    // Step 2: Uniqueness — any two solutions to φ are equal (by mutual minimality)
    val unique = have(
      (R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x)),
       R ⊆ S /\ reflexive(S)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (S ⊆ x)))
      |- (Q === S)
    ) subproof {
      assume(R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x)))
      assume(R ⊆ S /\ reflexive(S)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (S ⊆ x)))
      // Q ⊆ S: Q's minimality applied to S
      val qSubS = have(Q ⊆ S) subproof {
        have(∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x))) by Tautology
        val instS = thenHave(reflexive(S)(X) /\ (R ⊆ S) ==> (Q ⊆ S)) by InstantiateForall(S)
        have(thesis) by Tautology.from(instS)
      }
      // S ⊆ Q: S's minimality applied to Q
      val sSubQ = have(S ⊆ Q) subproof {
        have(∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (S ⊆ x))) by Tautology
        val instQ = thenHave(reflexive(Q)(X) /\ (R ⊆ Q) ==> (S ⊆ Q)) by InstantiateForall(Q)
        have(thesis) by Tautology.from(instQ)
      }
      have(thesis) by Tautology.from(qSubS, sSubQ, Subset.doubleInclusion of (x := Q, y := S))
    }

    // Step 3: ∃!(Q, φ(Q))
    val existsOne = have(∃!(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x)))) subproof {
      val exWitness = have(∃(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x)))) subproof {
        have(thesis) by RightExists(satisfies)
      }
      val allUnique = have(∀(Q, ∀(S, (R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x))) /\ (R ⊆ S /\ reflexive(S)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (S ⊆ x))) ==> (Q === S)))) subproof {
        have((R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x))) /\ (R ⊆ S /\ reflexive(S)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (S ⊆ x))) ==> (Q === S)) by Tautology.from(unique)
        thenHave(∀(S, (R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x))) /\ (R ⊆ S /\ reflexive(S)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (S ⊆ x))) ==> (Q === S))) by RightForall
        thenHave(thesis) by RightForall
      }
      have(thesis) by Tautology.from(
        exWitness,
        allUnique,
        Quantifiers.existsOneAlternativeDefinition of (P := λ(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x))))
      )
    }

    // Step 4: R ∪ Δ(X) === ε(Q, φ(Q)) by existsOneEpsilonUniqueness
    val epsilonEq = have((R ∪ Δ(X)) === ε(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x)))) subproof {
      have(thesis) by Tautology.from(
        existsOne,
        satisfies,
        Quantifiers.existsOneEpsilonUniqueness of (
          P := λ(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x))),
          y := (R ∪ Δ(X))
        )
      )
    }

    // Step 5: rewrite LHS as reflexiveClosure(R)(X) and RHS as closure(R)(λ(R, reflexive(R)(X)))
    // First get the beta-reduced form of closure.definition
    val closureDef = have(closure(R)(λ(R, reflexive(R)(X))) === ε(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(x, reflexive(x)(X) /\ (R ⊆ x) ==> (Q ⊆ x)))) by Congruence.from(
      closure.definition of (R := R, P := λ(R, reflexive(R)(X)))
    )
    have(thesis) by Congruence.from(
      epsilonEq,
      reflexiveClosure.definition of (R := R, X := X),
      closureDef
    )
  }

  /**
   * TODO: Define the transitive closure and transitive, reflexive closure.
   */
}
