import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau
import lisa.automation.Tautology
import lisa.automation.atp.Egg
import lisa.automation.atp.Goeland

object Example extends lisa.Main:
  draft()
  val A = variable[Prop]
  val B = variable[Prop]
  val C = variable[Prop]

  def normalForm[T:Sort](f: Expr[T]): Expr[T] =
    asFrontExpression(K.reducedForm(f.underlying)).asInstanceOf[Expr[T]]
  def findBestAtom(f: Expr[Prop]): Expr[Prop] =
    asFrontExpression(Tautology.findBestAtom(f.underlying).get).asInstanceOf

  extension (f: Expr[Prop]) {
    def substitute(a: Expr[Prop], b: Expr[Prop]): Expr[Prop] = ???
  }

  def dpll(using proof: library.Proof)(_f: Expr[Prop]): proof.ProofTacticJudgement = 
    TacticSubproof {
      val f = normalForm(_f)     //computes OL-normal form
      if f == True then have(f) by Hypothesis
      else if f == False then return proof.InvalidProofTactic("Not a Tautology")
      else
        val a = findBestAtom(f)
        val recStep1 = dpll(f.substitute(a, ⊤))
        val step1 = if recStep1.isValid then 
          have(a |- f) by Substitute(⊤ <=> a)(have(recStep1))
        else 
          return proof.InvalidProofTactic("Failed to prove f under a")
        have(dpll(f.substitute(a, False)));
        val step2 = thenHave(!a |- f) by Substitute(False <=> a)
        have(f) by Cut(step1, step2)
    }

  val thm = Theorem(
    (A \/ B) /\ (!A \/ C) ==> (B \/ C)
  ) {
    have(dpll(thesis.right.head))
  }



/*
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val thing : set = x
  extension (x: Expr[Set]) {
    inline infix def subset(y: Expr[Set]): Expr[Prop] = App(App(⊆, x), y)
  }
  // Simple proof with LISA's DSL
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    val a1 = assume(∀(x, P(x) ==> P(f(x))))
    have(thesis) by Tautology.from(a1 of x, a1 of f(x))
  }

  // Example of set theoretic development
  val union = Theorem(
    //App(App(⊆, x), y)
    //⊆.#@(x).#@(y)
    (thing) subset (thing)
  ) {
    sorry
  }
  
  /**
 * Theorem --- The empty set is a subset of every set.
 *
   *    `|- ∅ ⊆ x`
 */
  val leftEmpty = Theorem(
    P(x) //∅ ⊆ x
  ) {
    //have((y ∈ ∅) ==> (y ∈ x)) by Weakening(emptySetAxiom of (x := y))
    //val rhs = thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    //have(thesis) by Tautology.from(subsetAxiom of (x := ∅, y := x), rhs)
  }

  /**
 * Theorem --- If a set has an element, then it is not the empty set.
 *
   *    `y ∈ x ⊢ ! x = ∅`
 */
  val setWithElementNonEmpty = Theorem(
    (y ∈ x) |- x =/= ∅
  ) {
    have((x === ∅) |- !(y ∈ x)) by Substitute(x === ∅)(emptySetAxiom of (x := y))
  }

  /**
 * Theorem --- A power set is never empty.
 *
   *   `|- !powerAxiom(x) = ∅`
 */
  val powerSetNonEmpty = Theorem(
    𝒫(x) =/= ∅
  ) {
    have(thesis) by Tautology.from(
      setWithElementNonEmpty of (y := ∅, x := 𝒫(x)),
      powerSetAxiom of (x := ∅, y := x),
      leftEmpty
    )
  }

  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Tableau
  }


/**
 * Example showing discharge of proofs using the Goeland theorem prover. Will
 * fail if Goeland is not available on PATH.
 */
object ATPExample extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))):
    have(thesis) by Goeland

  val rule8 = Axiom(forall(x, x === f(f(f(f(f(f(f(f(x))))))))))
  val rule5 = Axiom(forall(x, x === f(f(f(f(f(x)))))))

  val saturation = Theorem(∅ === f(∅)):
    have(thesis) by Egg.from(rule8, rule5)
 */
