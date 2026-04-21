import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.{Substitution, Congruence}
import Base.{replace, toFormula, findBestAtom}

object Example extends lisa.Main:
  // draft mode; only proofs from the current file are checked
  draft()

  // first-order variables
  val a = variable[Prop]
  val b = variable[Prop]
  val c = variable[Prop]
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  // we can use scala extensions to define custom syntax
  extension (x: Expr[Ind])
    inline infix def subset(y: Expr[Ind]): Expr[Prop] = ⊆(x)(y)

  // Example of set theoretic development
  /**
    * Theorem --- a set is a subset of itself.
    * 
    *  `|- x ⊆ x`
    */
  val union = Theorem(
    x subset x
  ) {
    have((y ∈ x) ==> (y ∈ x)) by Restate
    thenHave(∀(y, (y ∈ x) ==> (y ∈ x))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := x, y := x))
  }

  /**
   * Theorem --- The empty set is a subset of every set.
   * 
   *   `|- ∅ ⊆ x`
   */
  val leftEmpty = Theorem(∅ ⊆ x): // braceless syntax is also fine!
    have((y ∈ ∅) ==> (y ∈ x)) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := ∅, y := x))
  
  /**
   * Theorem --- If a set has an element, then it is not the empty set.
   * 
   *   `y ∈ x ⊢ ! x = ∅`
   */
  val setWithElementNonEmpty = Theorem(
    (y ∈ x) |- x =/= ∅
  ) {
    have((x === ∅) |- !(y ∈ x)) by Substitute(x === ∅)(emptySetAxiom of (x := y))
    // this statement is `Restate` equivalent to the result, so we are done!
  }

  /**
   * Theorem --- the power set of any set is non-empty.
   * 
   *  `|- 𝒫(x) =/= ∅`
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

  // example showing the Tableau tactic to discharge first-order tautologies
  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Tableau
  }


  def dpll(using proof: library.Proof)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof :
    val f = normalForm(bot.right.head)     //computes OL-normal form
    if f == ⊤ then have(bot) by Restate
    else if f == ⊥ then throw Exception("Not a tautology")
    else
      val a = findBestAtom(f)

      have(dpll(f.replace(a,  ⊤)))
      thenHave(⊤ <=> a |- f) by Congruence
      val step1 = thenHave(a |- f) by Restate.from //subproof 1

      have(dpll(f.replace(a,  ⊥)))
      thenHave(⊥ <=> a |-f) by Congruence
      val step2 = thenHave(() |- (a, f)) by Restate.from //subproof 2

      have(f) by Cut(step2, step1)
      thenHave(bot) by Restate

    

  val testTheorem = Lemma(((a /\ b) \/ (a /\ c)) <=> (a /\ (b \/ c))) {
    have(dpll(thesis))
  }

