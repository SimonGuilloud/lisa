package lisa.prooflib
import lisa.fol.FOL as F
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.*
import lisa.utils.K
import lisa.utils.KernelHelpers.{|- => `K|-`, _}
import lisa.utils.UserLisaException
import lisa.utils.unification.UnificationUtils

object BasicStepTactic {
/*
  def unwrapTactic(using lib: Library, proof: lib.Proof)(using tactic: ProofTactic)(judgement: proof.ProofTacticJudgement)(message: String): proof.ProofTacticJudgement = {
    judgement match {
      case j: proof.ValidProofTactic => proof.ValidProofTactic(j.bot, j.scps, j.imports)
      case j: proof.InvalidProofTactic => proof.InvalidProofTactic(s"Internal tactic call failed! $message\n${j.message}")
    }
  }

  object Hypothesis extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      val intersectedPivot = botK.left.intersect(botK.right)

      if (intersectedPivot.isEmpty)
        proof.InvalidProofTactic("A formula for input to Hypothesis could not be inferred from left and right side of the sequent.")
      else
        proof.ValidProofTactic(bot, Seq(K.Hypothesis(botK, intersectedPivot.head)), Seq())
    }
  }

  object Rewrite extends ProofTactic with ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      if (!K.isSameSequent(botK, proof.getSequent(premise).underlying))
        proof.InvalidProofTactic("The premise and the conclusion are not trivially equivalent.")
      else
        proof.ValidProofTactic(bot, Seq(K.Restate(botK, -1)), Seq(premise))
    }
  }

  object RewriteTrue extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      if (!K.isSameSequent(botK, () `K|-` K.top))
        proof.InvalidProofTactic("The desired conclusion is not a trivial tautology.")
      else
        proof.ValidProofTactic(bot, Seq(K.RestateTrue(botK)), Seq())
    }
  }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |- Δ, Π
   * </pre>
   */
  object Cut extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1).underlying
      lazy val rightSequent = proof.getSequent(prem2).underlying
      val botK = bot.underlying
      val phiK = phi.underlying

      if (!K.contains(leftSequent.right, phiK))
        proof.InvalidProofTactic("Right-hand side of first premise does not contain φ as claimed.")
      else if (!K.contains(rightSequent.left, phiK))
        proof.InvalidProofTactic("Left-hand side of second premise does not contain φ as claimed.")
      else if (!K.isSameSet(botK.left + phiK, leftSequent.left ++ rightSequent.left) || (leftSequent.left.contains(phiK) && !botK.left.contains(phiK)))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the union of the left-hand sides of the premises.")
      else if (!K.isSameSet(botK.right + phiK, leftSequent.right ++ rightSequent.right) || (rightSequent.right.contains(phiK) && !botK.right.contains(phiK)))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the union of the right-hand sides of the premises.")
      else
        proof.ValidProofTactic(bot, Seq(K.Cut(botK, -1, -2, phiK)), Seq(prem1, prem2))
    }

    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)

      lazy val cutSet = (((rightSequent --<? bot).left |- ()) ++? ((leftSequent -->? bot).right |- ())).left
      lazy val intersectedCutSet = rightSequent.left intersect leftSequent.right

      if (!cutSet.isEmpty)
        if (cutSet.tail.isEmpty)
          Cut.withParameters(cutSet.head)(prem1, prem2)(bot)
        else
          proof.InvalidProofTactic("Inferred cut pivot is not a singleton set.")
      else if (!intersectedCutSet.isEmpty && intersectedCutSet.tail.isEmpty)
        // can still find a pivot
        Cut.withParameters(intersectedCutSet.head)(prem1, prem2)(bot)
      else
        proof.InvalidProofTactic("A consistent cut pivot cannot be inferred from the premises. Possibly a missing or extraneous clause.")
    }
  }

  // Left rules
  /**
   * <pre>
   *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
   * --------------     or     --------------
   *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
   * </pre>
   */
  object LeftAnd extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, psi: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      val psiK = psi.underlying
      lazy val phiAndPsi = phiK /\ psiK 

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the conclusion is not the same as the right-hand side of the premise.")
      else if (
        !K.isSameSet(botK.left + phiK, premiseSequent.left + phiAndPsi) &&
        !K.isSameSet(botK.left + psiK, premiseSequent.left + phiAndPsi) &&
        !K.isSameSet(botK.left + phiK + psiK, premiseSequent.left + phiAndPsi)
      )
        proof.InvalidProofTactic("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftAnd(botK, -1, phiK, psiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case F.App(F.App(F.and, phi), psi) =>
            if (premiseSequent.left.contains(phi))
              LeftAnd.withParameters(phi, psi)(premise)(bot)
            else
              LeftAnd.withParameters(phi, psi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (F.isSameSequent(premiseSequent, bot))
        unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial LeftAnd failed.")
      else
        proof.InvalidProofTactic("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  object LeftOr extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(disjuncts: F.Formula*)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_).underlying)
      val botK = bot.underlying
      val disjunctsK = disjuncts.map(_.underlying)
      lazy val disjunction = K.multior(disjunctsK)

      if (premises.length == 0)
        proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (premises.length != disjuncts.length)
        proof.InvalidProofTactic(s"Premises and disjuncts expected to be equal in number, but ${premises.length} premises and ${disjuncts.length} disjuncts received.")
      else if (!K.isSameSet(botK.right, premiseSequents.map(_.right).reduce(_ union _)))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
      else if (
        premiseSequents.zip(disjunctsK).forall((sequent, disjunct) => K.isSubset(sequent.left, botK.left + disjunct)) // \forall i. premise_i.left \subset bot.left + phi_i
        && !K.isSubset(botK.left, premiseSequents.map(_.left).reduce(_ union _) + disjunction) // bot.left \subseteq \bigcup premise_i.left
      )
        proof.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftOr(botK, Range(-1, -premises.length - 1, -1), disjunctsK)), premises.toSeq)
    }

    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (premises.length == 0) proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty)) {
        val emptyIndex = pivots.indexWhere(_.isEmpty)
        if (F.isSubset(premiseSequents(emptyIndex).left, bot.left))
          unwrapTactic(Weakening(premises(emptyIndex))(bot))("Attempted weakening on trivial premise for LeftOr failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the one of the premises.")
      } else if (pivots.forall(_.tail.isEmpty))
        LeftOr.withParameters(pivots.map(_.head)*)(premises*)(bot)
      else
        // some extraneous formulae
        proof.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
    }
  }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ⇒ψ |- Δ, Π
   * </pre>
   */
  object LeftImplies extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, psi: F.Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1).underlying
      lazy val rightSequent = proof.getSequent(prem2).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      val psiK = psi.underlying
      lazy val implication = (phiK ==> psiK)

      if (!K.isSameSet(botK.right + phiK, leftSequent.right union rightSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the union of right-hand sides of premises.")
      else if (!K.isSameSet(botK.left + psiK, leftSequent.left union rightSequent.left + implication))
        proof.InvalidProofTactic("Left-hand side of conclusion + ψ is not the union of left-hand sides of premises + φ⇒ψ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftImplies(botK, -1, -2, phiK, psiK)), Seq(prem1, prem2))
    }
    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)
      lazy val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        if (F.isSubset(leftSequent.left, bot.left))
          unwrapTactic(Weakening(prem1)(bot))("Attempted weakening on trivial left premise for LeftImplies failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the first premises.")
      else if (pivotRight.isEmpty)
        if (F.isSubset(rightSequent.right, bot.right))
          unwrapTactic(Weakening(prem2)(bot))("Attempted weakening on trivial right premise for LeftImplies failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the second premises.")
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        LeftImplies.withParameters(pivotLeft.head, pivotRight.head)(prem1, prem2)(bot)
      else
        proof.InvalidProofTactic("Could not infer an implication as a pivot from the premises and conclusion, possible extraneous formulae in premises.")
    }
  }

  /**
   * <pre>
   *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ⇔ψ |- Δ                 Γ, φ⇔ψ |- Δ
   * </pre>
   */
  object LeftIff extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, psi: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      val psiK = psi.underlying
      lazy val implication = phiK <=> psiK
      lazy val impLeft = phiK ==> psiK
      lazy val impRight = psiK ==> phiK

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of premise is not the same as right-hand side of conclusion.")
      else if (
        !K.isSameSet(botK.left + impLeft, premiseSequent.left + implication) &&
        !K.isSameSet(botK.left + impRight, premiseSequent.left + implication) &&
        !K.isSameSet(botK.left + impLeft + impRight, premiseSequent.left + implication)
      )
        proof.InvalidProofTactic("Left-hand side of premise + φ⇔ψ is not the same as left-hand side of conclusion + either φ⇒ψ, ψ⇒φ or both.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftIff(botK, -1, phiK, psiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftIff failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else
        pivot.head match {
          case F.App(F.App(F.implies, phi), psi) => LeftIff.withParameters(phi, psi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a pivot implication from premise.")
        }
    }
  }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  object LeftNot extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      lazy val negation = !phiK

      if (!K.isSameSet(botK.right + phiK, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")
      else if (!K.isSameSet(botK.left, premiseSequent.left + negation))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise + ¬φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftNot(botK, -1, phiK)), Seq(premise))
    }
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftNot failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (!pivot.isEmpty && pivot.tail.isEmpty)
        LeftNot.withParameters(pivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")

    }
  }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *   Γ, ∀x. φ |- Δ
   *
   * </pre>
   */
  object LeftForall extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, x: F.Variable[F.T], t: F.Term)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val tK = t.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.forall(xK, phiK)
      lazy val instantiated = K.substituteVariables(phiK, Map(xK -> tK))

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!K.isSameSet(botK.left + instantiated, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftForall(botK, -1, phiK, xK, tK)), Seq(premise))
    }

    def withParameters(using lib: Library, proof: lib.Proof)(t: F.Term)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left // .diff(botK.left)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case F.forall(x, phi) => LeftForall.withParameters(phi, x, t)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftForall failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Formula = instantiatedPivot.head
        val quantifiedPhi: Option[F.Formula] = bot.left.find(f =>
          f match {
            case g @ F.forall(v, e) => F.isSame(e.substitute(v := t), in)
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(F.forall(x, phi)) => LeftForall.withParameters(phi, x, t)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val prepivot = bot.left.diff(premiseSequent.left)
      lazy val pivot = if (prepivot.isEmpty) bot.left else prepivot
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftForall failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Formula = instantiatedPivot.head
        val quantifiedPhi: Option[F.Formula] = pivot.find(f =>
          f match {
            case g @ F.forall(x, phi) => UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVars - x)).isDefined
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(F.forall(x, phi)) =>
            LeftForall.withParameters(phi, x, ??? /* TODO UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVars - x)).get._2.getOrElse(x, x)*/)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
    }
  }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  object LeftExists extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, x: F.Variable[F.T])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.exists(xK, phiK)

      if ((botK.left union botK.right).exists(_.freeVariables.contains(xK)))
        proof.InvalidProofTactic("The variable x must not be free in the resulting sequent.")
      else if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!K.isSameSet(botK.left + phiK, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftExists(botK, -1, phiK, xK)), Seq(premise))
    }

    var debug = false
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for LeftExists failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          val in: F.Formula = instantiatedPivot.head
          val quantifiedPhi: Option[F.Formula] = bot.left.find(f =>
            f match {
              case F.exists(_, g) => F.isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(F.exists(x, phi)) => LeftExists.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Ambigous application of LeftExists, multiple pivots corresponding to the unquantified formula found.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.exists(x, phi) => LeftExists.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Ambigous application of LeftExists, multiple pivots corresponding to the quantified formula found.")
    }
  }

  /*
  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ⇔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  object LeftExistsOne extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, x: F.Variable[F.T])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val y = K.Variable(lisa.utils.KernelHelpers.freshId(phiK.freeVariables.map(_.id), x.id), K.Term)
      lazy val instantiated = K.exists(y, K.forall(xK, (xK === y) <=> phiK ))
      lazy val quantified = K.ExistsOne(xK, phiK)

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise.")
      else if (!K.isSameSet(botK.left + instantiated, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + ∃y.∀x. (x=y) ⇔ φ is not the same as left-hand side of premise + ∃!x. φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftExistsOne(botK, -1, phiK, xK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for LeftExistsOne failed.")
          else
            proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ⇔ φ == extract ==> x, phi
            case F.exists(_, F.forall(x, F.AppliedConnector(F.Iff, Seq(_, phi)))) => LeftExistsOne.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.BinderFormula(F.ExistsOne, x, phi) => LeftExistsOne.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
    }
  }

  */

  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  object RightAnd extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(conjuncts: F.Formula*)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_).underlying)
      lazy val botK = bot.underlying
      lazy val conjunctsK = conjuncts.map(_.underlying)
      lazy val conjunction = K.multiand(conjunctsK)

      if (premises.length == 0)
        proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (premises.length != conjuncts.length)
        proof.InvalidProofTactic(s"Premises and conjuncts expected to be equal in number, but ${premises.length} premises and ${conjuncts.length} conjuncts received.")
      else if (!K.isSameSet(botK.left, premiseSequents.map(_.left).reduce(_ union _)))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (
        premiseSequents.zip(conjunctsK).forall((sequent, conjunct) => K.isSubset(sequent.right, botK.right + conjunct)) // \forall i. premise_i.right \subset bot.right + phi_i
        && !K.isSubset(botK.right, premiseSequents.map(_.right).reduce(_ union _) + conjunction) // bot.right \subseteq \bigcup premise_i.right
      )
        proof.InvalidProofTactic("Right-hand side of conclusion + conjuncts is not the same as the union of the right-hand sides of the premises + φ∧ψ....")
      else
        proof.ValidProofTactic(bot, Seq(K.RightAnd(botK, Range(-1, -premises.length - 1, -1), conjunctsK)), premises)
    }

    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (premises.length == 0) proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty)) {
        val emptyIndex = pivots.indexWhere(_.isEmpty)
        if (F.isSubset(premiseSequents(emptyIndex).left, bot.left))
          unwrapTactic(Weakening(premises(emptyIndex))(bot))("Attempted weakening on trivial premise for RightAnd failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the one of the premises.")
      } else if (pivots.forall(_.tail.isEmpty))
        RightAnd.withParameters(pivots.map(_.head)*)(premises*)(bot)
      else
        // some extraneous formulae
        proof.InvalidProofTactic("Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises +φ∧ψ.")
    }
  }

  /**
   * <pre>
   *   Γ |- φ, Δ               Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  object RightOr extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, psi: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val psiK = psi.underlying
      lazy val botK = bot.underlying
      lazy val phiAndPsi = phiK \/ psiK

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of the premise is not the same as the left-hand side of the conclusion.")
      else if (
        !K.isSameSet(botK.right + phiK, premiseSequent.right + phiAndPsi) &&
        !K.isSameSet(botK.right + psiK, premiseSequent.right + phiAndPsi) &&
        !K.isSameSet(botK.right + phiK + psiK, premiseSequent.right + phiAndPsi)
      )
        proof.InvalidProofTactic("Right-hand side of premise + φ∧ψ is not the same as right-hand side of conclusion + either φ, ψ or both.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightOr(botK, -1, phiK, psiK)), Seq(premise))
    }
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case F.App(F.App(F.or, phi), psi) =>
            if (premiseSequent.left.contains(phi))
              RightOr.withParameters(phi, psi)(premise)(bot)
            else
              RightOr.withParameters(psi, phi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (F.isSameSequent(premiseSequent, bot))
        unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightOr failed.")
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ∧ψ is not the same as right-hand side of premise + either φ, ψ or both.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ⇒ψ, Δ
   * </pre>
   */
  object RightImplies extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, psi: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val psiK = psi.underlying
      lazy val botK = bot.underlying
      lazy val implication = phiK ==> psiK

      if (!K.isSameSet(botK.left + phiK, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + psiK, premiseSequent.right + implication))
        proof.InvalidProofTactic("Right-hand side of conclusion + ψ is not the same as right-hand side of premise + φ⇒ψ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightImplies(botK, -1, phiK, psiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val leftPivot = premiseSequent.left.diff(bot.left)
      lazy val rightPivot = premiseSequent.right.diff(bot.right)

      if (
        !leftPivot.isEmpty && leftPivot.tail.isEmpty &&
        !rightPivot.isEmpty && rightPivot.tail.isEmpty
      )
        RightImplies.withParameters(leftPivot.head, rightPivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Could not infer an implication as pivot from premise and conclusion.")
    }
  }

  /**
   * <pre>
   *  Γ |- φ⇒ψ, Δ    Σ |- ψ⇒φ, Π
   * ----------------------------
   *      Γ, Σ |- φ⇔ψ, Π, Δ
   * </pre>
   */
  object RightIff extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, psi: F.Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1).underlying
      lazy val rightSequent = proof.getSequent(prem2).underlying
      lazy val phiK = phi.underlying
      lazy val psiK = psi.underlying
      lazy val botK = bot.underlying
      lazy val implication = phiK <=> psiK
      lazy val impLeft = phiK ==> psiK
      lazy val impRight = psiK ==> phiK

      if (!K.isSameSet(botK.left, leftSequent.left union rightSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (!K.isSubset(leftSequent.right, botK.right + impLeft))
        proof.InvalidProofTactic(
          "Conclusion is missing the following formulas from the left premise: " + (leftSequent.right -- botK.right).map(f => s"[${f.repr}]").reduce(_ ++ ", " ++ _)
        )
      else if (!K.isSubset(rightSequent.right, botK.right + impRight))
        proof.InvalidProofTactic(
          "Conclusion is missing the following formulas from the right premise: " + (rightSequent.right -- botK.right).map(f => s"[${f.repr}]").reduce(_ ++ ", " ++ _)
        )
      else if (!K.isSubset(botK.right, leftSequent.right union rightSequent.right + implication))
        proof.InvalidProofTactic(
          "Conclusion has extraneous formulas apart from premises and implication: " ++ (botK.right
            .removedAll(leftSequent.right union rightSequent.right + implication))
            .map(f => s"[${f.repr}]")
            .reduce(_ ++ ", " ++ _)
        )
      else
        proof.ValidProofTactic(bot, Seq(K.RightIff(botK, -1, -2, phiK, psiK)), Seq(prem1, prem2))
    }

    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(prem1)
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(prem1)(bot))("Attempted weakening on trivial premise for RightIff failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.App(F.App(F.implies, phi), psi) => RightIff.withParameters(phi, psi)(prem1, prem2)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an implication as pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ⇒ψ + ψ⇒φ is not the same as the union of the right-hand sides of the premises φ⇔ψ.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  object RightNot extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val negation = !phiK

      if (!K.isSameSet(botK.left + phiK, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right, premiseSequent.right + negation))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise + ¬φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightNot(botK, -1, phiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightIff failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (pivot.tail.isEmpty)
        RightNot.withParameters(pivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")

    }
  }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  object RightForall extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, x: F.Variable[F.T])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.forall(xK, phiK)

      if ((botK.left union botK.right).exists(_.freeVariables.contains(xK)))
        proof.InvalidProofTactic("The variable x is free in the resulting sequent.")
      else if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + phiK, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∀x. φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightForall(botK, -1, phiK, xK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightForall failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from the premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          val in: F.Formula = instantiatedPivot.head
          val quantifiedPhi: Option[F.Formula] = bot.right.find(f =>
            f match {
              case F.forall(_, g) => F.isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(F.forall(x, phi)) => RightForall.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.forall(x, phi) => RightForall.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  /**
   * <pre>
   *   Γ |- φ[t/x], Δ
   * -------------------
   *  Γ |- ∃x. φ, Δ
   *
   * (ln-x stands for locally nameless x)
   * </pre>
   */
  object RightExists extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, x: F.Variable[F.T], t: F.Term)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val tK = t.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.exists(xK, phiK)
      lazy val instantiated = K.substituteVariables(phiK, Map(xK -> tK))

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise")
      else if (!K.isSameSet(botK.right + instantiated, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ")
      else
        proof.ValidProofTactic(bot, Seq(K.RightExists(botK, -1, phiK, xK, tK)), Seq(premise))
    }

    def withParameters(using lib: Library, proof: lib.Proof)(t: F.Term)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case F.exists(x, phi) => RightExists.withParameters(phi, x, t)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
      else if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightExists failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Formula = instantiatedPivot.head
        val quantifiedPhi: Option[F.Formula] = bot.right.find(f =>
          f match {
            case g @ F.exists(v, e) => F.isSame(e.substitute(v := t), in)
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(F.exists(x, phi)) => RightExists.withParameters(phi, x, t)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val prepivot = bot.right.diff(premiseSequent.right)
      lazy val pivot = if (prepivot.isEmpty) bot.right else prepivot
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightForall failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Formula = instantiatedPivot.head

        val quantifiedPhi: Option[F.Formula] = pivot.find(f =>
          f match {
            case g @ F.exists(x, phi) =>
              UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVars - x)).isDefined
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(F.exists(x, phi)) =>
            RightExists.withParameters(phi, x, ??? /* TODO UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVars - x)).get._2.getOrElse(x, x)*/)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  /*
  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ⇔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  object RightExistsOne extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Formula, x: F.Variable)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val y = K.Variable(lisa.utils.KernelHelpers.freshId(phiK.freeVariables.map(_.id), x.id))
      lazy val instantiated = K.BinderFormula(
        K.Exists,
        y,
        K.BinderFormula(
          K.Forall,
          xK,
          K.ConnectorFormula(K.Iff, List(K.AtomicFormula(K.equality, List(K.VariableTerm(xK), K.VariableTerm(y))), phiK))
        )
      )
      lazy val quantified = K.BinderFormula(K.ExistsOne, xK, phiK)

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + instantiated, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + ∃y.∀x. (x=y) ⇔ φ is not the same as right-hand side of premise + ∃!x. φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightExistsOne(botK, -1, phiK, xK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightExistsOne failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ⇔ φ == extract ==> x, phi
            case F.exists(_, F.forall(x, F.AppliedConnector(F.Iff, Seq(_, phi)))) =>
              RightExistsOne.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.BinderFormula(F.ExistsOne, x, phi) => RightExistsOne.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  */

  object RightBeta extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)
    (phi: F.Formula, lambda: F.Abs[?, ?], t: F.Expr[?], x: F.Variable[?])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val lambdaK = lambda.underlying
      lazy val tK = t.underlying
      lazy val xK = x.underlying
      lazy val botK = bot.underlying
      lazy val y = lambda.v.underlying
      lazy val e = lambda.body.underlying
      if (phi.sort != K.Formula) 
        return proof.InvalidProofTactic("φ must be a formula, but it is a " + phi.sort)
      else if (y.sort != t.sort) 
        return proof.InvalidProofTactic("y must have the same type as t, but they are " + y.sort + " and " + t.sort)
      else if (e.sort != x.sort) 
        return proof.InvalidProofTactic("e must have the same type as x, but they are " + e.sort + " and " + x.sort)
      else if (K.isSameSet(botK.left, premiseSequent.left)) {
        val redex = lambdaK(tK)
        val normalized = K.substituteVariables(e, Map(y -> tK))
        val phi_redex = K.substituteVariables(phiK, Map(xK -> redex))
        val phi_normalized = K.substituteVariables(phiK, Map(xK -> normalized))
        if (K.isSameSet(botK.right + phi_redex, premiseSequent.right + phi_normalized) || K.isSameSet(botK.right + phi_normalized, premiseSequent.right + phi_redex))
          return proof.ValidProofTactic(bot, Seq(K.LeftBeta(botK, -1, phiK, lambdaK, tK, xK)), Seq(premise))
        else 
          return proof.InvalidProofTactic("Right-hand side of the conclusion + φ[λy.e]t/x must be the same as right-hand side of the premise + φ[e[t/y]/x] (or the opposite)")
      } else 
        return proof.InvalidProofTactic("Left-hand side of the conclusion must be the same as the left-hand side of the premise")
    }
  }

  object LeftBeta extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)
    (phi: F.Formula, lambda: F.Abs[?, ?], t: F.Expr[?], x: F.Variable[?])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val lambdaK = lambda.underlying
      lazy val tK = t.underlying
      lazy val xK = x.underlying
      lazy val botK = bot.underlying
      lazy val y = lambda.v.underlying
      lazy val e = lambda.body.underlying
      if (phi.sort != K.Formula) 
        return proof.InvalidProofTactic("φ must be a formula, but it is a " + phi.sort)
      else if (y.sort != t.sort) 
        return proof.InvalidProofTactic("y must have the same type as t, but they are " + y.sort + " and " + t.sort)
      else if (e.sort != x.sort) 
        return proof.InvalidProofTactic("e must have the same type as x, but they are " + e.sort + " and " + x.sort)
      else if (K.isSameSet(botK.right, premiseSequent.right)) {
        val redex = lambdaK(tK)
        val normalized = K.substituteVariables(e, Map(y -> tK))
        val phi_redex = K.substituteVariables(phiK, Map(xK -> redex))
        val phi_normalized = K.substituteVariables(phiK, Map(xK -> normalized))
        if (K.isSameSet(botK.left + phi_redex, premiseSequent.left + phi_normalized) || K.isSameSet(botK.left + phi_normalized, premiseSequent.left + phi_redex))
          return proof.ValidProofTactic(bot, Seq(K.LeftBeta(botK, -1, phiK, lambdaK, tK, xK)), Seq(premise))
        else 
          return proof.InvalidProofTactic("Left-hand side of the conclusion + φ[λy.e]t/x must be the same as left-hand side of the premise + φ[e[t/y]/x] (or the opposite)")
      } else 
        return proof.InvalidProofTactic("Right-hand side of the conclusion must be the same as the right-hand side of the premise")
    }
  }

  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  object Weakening extends ProofTactic with ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)

      if (!F.isImplyingSequent(premiseSequent, bot))
        proof.InvalidProofTactic("Conclusion cannot be trivially derived from premise.")
      else
        proof.ValidProofTactic(bot, Seq(K.Weakening(bot.underlying, -1)), Seq(premise))
    }
  }

  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  object LeftRefl extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(fa: F.Formula)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val faK = fa.underlying
      lazy val botK = bot.underlying

      if (!K.isSameSet(botK.left + faK, premiseSequent.left) || !premiseSequent.left.exists(_ == faK) || botK.left.exists(_ == faK))
        proof.InvalidProofTactic("Left-hand sides of the conclusion + φ is not the same as left-hand side of the premise.")
      else if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else
        faK match {
          case K.Application(K.Application(K.equality, left), right) =>
            if (K.isSame(left, right))
              proof.ValidProofTactic(bot, Seq(K.LeftRefl(botK, -1, faK)), Seq(premise))
            else
              proof.InvalidProofTactic("φ is not an instance of reflexivity.")
          case _ => proof.InvalidProofTactic("φ is not an equality.")
        }
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        LeftRefl.withParameters(pivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Could not infer an equality as pivot from premise and conclusion.")
    }
  }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  object RightRefl extends ProofTactic with ProofSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(fa: F.Formula)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val faK = fa.underlying
      lazy val botK = bot.underlying
      if (!botK.right.exists(_ == faK))
        proof.InvalidProofTactic("Right-hand side of conclusion does not contain φ.")
      else
        faK match {
          case K.Application(K.Application(K.equality, left), right) =>
            if (K.isSame(left, right))
              proof.ValidProofTactic(bot, Seq(K.RightRefl(botK, faK)), Seq())
            else
              proof.InvalidProofTactic("φ is not an instance of reflexivity.")
          case _ => proof.InvalidProofTactic("φ is not an equality.")
        }
    }

    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      if (bot.right.isEmpty) proof.InvalidProofTactic("Right-hand side of conclusion does not contain an instance of reflexivity.")
      else {
        // go through conclusion to see if you can find an reflexive formula
        val pivot: Option[F.Formula] = bot.right.find(f =>
          val Eq = F.equality // (F.equality: (F.|->[F.**[F.Term, 2], F.Formula]))
          f match {
            case F.App(F.App(e, l), r) =>
              (F.equality) == (e) && l == r // termequality
            case _ => false
          }
        )

        pivot match {
          case Some(phi) => RightRefl.withParameters(phi)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an equality as pivot from conclusion.")
        }

      }

    }
  }

  /**
   * <pre>
   *   Γ, φ(s) |- Δ     Σ |- s=t, Π     
   * --------------------------------
   *        Γ, Σ φ(t) |- Δ, Π
   * </pre>
   */
  object LeftSubstEq extends ProofTactic {

    def withParametersSimple[T1, T2](using lib: Library, proof: lib.Proof)(
      s: F.Expr[T1], t: F.Expr[T1], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[T1], F.Expr[2])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      withParameters(s, t, vars, lambdaPhi)(prem1, prem2)(bot)
    }

    def withParameters(using lib: Library, proof: lib.Proof)(
      s: F.Expr[?], t: F.Expr[?], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[?], F.Expr[?])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent1 = proof.getSequent(prem1).underlying
      lazy val premiseSequent2 = proof.getSequent(prem2).underlying
      lazy val botK = bot.underlying
      lazy val sK = s.underlying
      lazy val tK = t.underlying
      lazy val varsK = vars.map(_.underlying)
      val lambdaPhiK = (lambdaPhi._1.underlying, lambdaPhi._2.underlying)
      val (phi_arg, phi_body) = lambdaPhiK

      if (s.sort != phi_arg.sort || t.sort != phi_arg.sort) 
        return proof.InvalidProofTactic("The types of the variable of φ must be the same as the types of s and t.")
      else if (!s.sort.isFunctional) 
        return proof.InvalidProofTactic("Can only substitute function-like terms (with type _ -> ... -> _ -> Term)")
      val phi_s_for_f = K.substituteVariables(phi_body, Map(phi_arg -> sK))
      val phi_t_for_f = K.substituteVariables(phi_body, Map(phi_arg -> tK))

      val inner1 = varsK.foldLeft(sK)(_(_))
      val inner2 = varsK.foldLeft(tK)(_(_))
      val sEqt = K.equality(inner1)(inner2)
      val varss = varsK.toSet

      if (
        K.isSubset(premiseSequent1.right, botK.right) &&
        K.isSubset(premiseSequent2.right, botK.right + sEqt) &&
        K.isSubset(botK.right, premiseSequent1.right union premiseSequent2.right)
      ) {
        if (
          K.isSubset(premiseSequent1.left, botK.left + phi_s_for_f) &&
          K.isSubset(premiseSequent2.left, botK.left) &&
          K.isSubset(botK.left, premiseSequent1.left union premiseSequent2.left + phi_t_for_f)
        ) {
          if ( 
            premiseSequent2.left.exists(f => f.freeVariables.intersect(varss).nonEmpty) || 
            premiseSequent2.right.exists(f => !K.isSame(f, sEqt) && f.freeVariables.intersect(varss).nonEmpty)
          ) {
            return proof.InvalidProofTactic("The variable x1...xn must not be free in the second premise other than as parameters of the equality.")
          } else  proof.ValidProofTactic(bot, Seq(K.LeftSubstEq(botK, -1, -2, sK, tK, varsK, lambdaPhiK)), Seq(prem1, prem2))
        }
        else return proof.InvalidProofTactic("Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_).")
      }
      else return proof.InvalidProofTactic("Right-hand sides of the premise and the conclusion aren't the same.")
      

    }
  }

  /**
   * <pre>
   *  Γ |- φ(s), Δ     Σ |- s=t, Π
   * ---------------------------------
   *         Γ, Σ |- φ(t), Δ, Π
   * </pre>
   */
  object RightSubstEq extends ProofTactic {
    def withParametersSimple[T1](using lib: Library, proof: lib.Proof)(
      s: F.Expr[T1], t: F.Expr[T1], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[T1], F.Expr[F.F])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      withParameters(s, t, vars, lambdaPhi)(prem1, prem2)(bot)
    }

    def withParameters(using lib: Library, proof: lib.Proof)(
      s: F.Expr[?], t: F.Expr[?], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[?], F.Formula)
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent1 = proof.getSequent(prem1).underlying
      lazy val premiseSequent2 = proof.getSequent(prem2).underlying
      lazy val botK = bot.underlying
      lazy val sK = s.underlying
      lazy val tK = t.underlying
      lazy val varsK = vars.map(_.underlying)
      val lambdaPhiK = (lambdaPhi._1.underlying, lambdaPhi._2.underlying)
      val (phi_arg, phi_body) = lambdaPhiK

      if (s.sort != phi_arg.sort || t.sort != phi_arg.sort) 
        return proof.InvalidProofTactic("The types of the variable of φ must be the same as the types of s and t.")
      else if (!s.sort.isFunctional) 
        return proof.InvalidProofTactic("Can only substitute function-like terms (with type _ -> ... -> _ -> Term)")
      val phi_s_for_f = K.substituteVariables(phi_body, Map(phi_arg -> sK))
      val phi_t_for_f = K.substituteVariables(phi_body, Map(phi_arg -> tK))

      val inner1 = varsK.foldLeft(sK)(_(_))
      val inner2 = varsK.foldLeft(tK)(_(_))
      val sEqt = K.equality(inner1)(inner2)
      val varss = varsK.toSet

      if (
        K.isSubset(premiseSequent1.right, botK.right) &&
        K.isSubset(premiseSequent2.right, botK.right + sEqt) &&
        K.isSubset(botK.right, premiseSequent1.right union premiseSequent2.right)
      ) {
        if (
          K.isSubset(premiseSequent1.left, botK.left + phi_s_for_f) &&
          K.isSubset(premiseSequent2.left, botK.left) &&
          K.isSubset(botK.left, premiseSequent1.left union premiseSequent2.left + phi_t_for_f)
        ) {
          if ( 
            premiseSequent2.left.exists(f => f.freeVariables.intersect(varss).nonEmpty) || 
            premiseSequent2.right.exists(f => !K.isSame(f, sEqt) && f.freeVariables.intersect(varss).nonEmpty)
          ) {
            proof.InvalidProofTactic("The variable x1...xn must not be free in the second premise other than as parameters of the equality.")
          } else proof.ValidProofTactic(bot, Seq(K.RightSubstEq(botK, -1, -2, sK, tK, varsK, lambdaPhiK)), Seq(prem1, prem2))
        }
        else proof.InvalidProofTactic("Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_).")
      }
      else proof.InvalidProofTactic("Right-hand sides of the premise and the conclusion aren't the same.")
    }

  }

  /**
   * <pre>
   *           Γ, φ(a1,...an) |- Δ
   * ----------------------------------------
   *  Γ, a1⇔b1, ..., an⇔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  object LeftSubstIff extends ProofTactic {
    def withParametersSimple[T1, T2](using lib: Library, proof: lib.Proof)(
      s: F.Expr[T1], t: F.Expr[T1], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[T1], F.Expr[2])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = 
      LeftSubstEq.withParametersSimple(s, t, vars, lambdaPhi)(prem1, prem2)(bot)

    def withParameters(using lib: Library, proof: lib.Proof)(
      s: F.Expr[?], t: F.Expr[?], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[?], F.Expr[?])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = 
      LeftSubstEq.withParameters(s, t, vars, lambdaPhi)(prem1, prem2)(bot)
      /*{
      lazy val premiseSequent1 = proof.getSequent(prem1).underlying
      lazy val premiseSequent2 = proof.getSequent(prem2).underlying
      lazy val botK = bot.underlying
      lazy val sK = s.underlying
      lazy val tK = t.underlying
      lazy val varsK = vars.map(_.underlying)
      val lambdaPhiK = (lambdaPhi._1.underlying, lambdaPhi._2.underlying)
      val (phi_arg, phi_body) = lambdaPhiK

      if (s.sort != phi_arg.sort || t.sort != phi_arg.sort) 
        return proof.InvalidProofTactic("The types of the variable of φ must be the same as the types of s and t.")
      else if (!s.sort.isFunctional) 
        return proof.InvalidProofTactic("Can only substitute function-like terms (with type _ -> ... -> _ -> Term)")
      val phi_s_for_f = K.substituteVariables(phi_body, Map(phi_arg -> sK))
      val phi_t_for_f = K.substituteVariables(phi_body, Map(phi_arg -> tK))

      val inner1 = varsK.foldLeft(sK)(_(_))
      val inner2 = varsK.foldLeft(tK)(_(_))
      val sEqt = K.Iff(inner1)(inner2)
      val varss = varsK.toSet

      if (
        K.isSubset(premiseSequent1.right, botK.right) &&
        K.isSubset(premiseSequent2.right, botK.right + sEqt) &&
        K.isSubset(botK.right, premiseSequent1.right union premiseSequent2.right)
      ) {
        if (
          K.isSubset(premiseSequent1.left, botK.left + phi_s_for_f) &&
          K.isSubset(premiseSequent2.left, botK.left) &&
          K.isSubset(botK.left, premiseSequent1.left union premiseSequent2.left + phi_t_for_f)
        ) {
          if ( 
            premiseSequent2.left.exists(f => f.freeVariables.intersect(varss).nonEmpty) || 
            premiseSequent2.right.exists(f => !K.isSame(f, sEqt) && f.freeVariables.intersect(varss).nonEmpty)
          ) {
            return proof.InvalidProofTactic("The variable x1...xn must not be free in the second premise other than as parameters of the equality.")
          } else  proof.ValidProofTactic(bot, Seq(K.LeftSubstEq(botK, -1, -2, sK, tK, varsK, lambdaPhiK)), Seq(prem1, prem2))
        }
        else return proof.InvalidProofTactic("Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_).")
      }
      else return proof.InvalidProofTactic("Right-hand sides of the premise and the conclusion aren't the same.")
      */

  }

  /**
   * <pre>
   *           Γ |- φ(a1,...an), Δ
   * ----------------------------------------
   *  Γ, a1⇔b1, ..., an⇔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  object RightSubstIff extends ProofTactic {
    def withParametersSimple[T1, T2](using lib: Library, proof: lib.Proof)(
      s: F.Expr[T1], t: F.Expr[T1], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[T1], F.Expr[2])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = 
      LeftSubstEq.withParametersSimple(s, t, vars, lambdaPhi)(prem1, prem2)(bot)

    def withParameters(using lib: Library, proof: lib.Proof)(
      s: F.Expr[?], t: F.Expr[?], vars: Seq[F.Variable[?]], lambdaPhi: (F.Variable[?], F.Expr[?])
    )(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = 
      LeftSubstEq.withParameters(s, t, vars, lambdaPhi)(prem1, prem2)(bot)

      /*
    def withParametersSimple(using lib: Library, proof: lib.Proof)(
        equals: List[(F.Formula, F.Formula)],
        lambdaPhi: F.LambdaExpression[F.Formula, F.Formula, ?]
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      withParameters(equals.map { case (a, b) => (F.lambda(Seq(), a), F.lambda(Seq(), b)) }, (lambdaPhi.bounds.asInstanceOf[Seq[F.SchematicAtomicLabel[?]]], lambdaPhi.body))(premise)(bot)
    }

    def withParameters(using lib: Library, proof: lib.Proof)(
        equals: List[(F.LambdaExpression[F.Term, F.Formula, ?], F.LambdaExpression[F.Term, F.Formula, ?])],
        lambdaPhi: (Seq[F.SchematicAtomicLabel[?]], F.Formula)
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {

      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val botK = bot.underlying
      lazy val equalsK = equals.map(p => (p._1.underlyingLTF, p._2.underlyingLTF))
      lazy val lambdaPhiK = (lambdaPhi._1.map(_.underlying), lambdaPhi._2.underlying)

      val (psi_s, tau_s) = equalsK.unzip
      val (phi_args, phi_body) = lambdaPhiK
      if (phi_args.size != psi_s.size)
        return proof.InvalidProofTactic("The number of arguments of φ must be the same as the number of equalities.")
      else if (equalsK.zip(phi_args).exists { case ((s, t), arg) => s.vars.size != arg.arity || t.vars.size != arg.arity })
        return proof.InvalidProofTactic("The arities of symbols in φ must be the same as the arities of equalities.")

      val phi_psi = K.instantiatePredicateSchemas(phi_body, (phi_args zip psi_s).toMap)
      val phi_tau = K.instantiatePredicateSchemas(phi_body, (phi_args zip tau_s).toMap)
      val psiIffTau = equalsK map { case (s, t) =>
        assert(s.vars.size == t.vars.size)
        val base = K.ConnectorFormula(K.Iff, Seq(s.body, if (s.vars == t.vars) t.body else t(s.vars.map(K.VariableTerm))))
        (s.vars).foldLeft(base: K.Formula) { case (acc, s_arg) => K.forall(s_arg, acc) }
      }

      if (!K.isSameSet(botK.left, premiseSequent.left ++ psiIffTau)) {
        proof.InvalidProofTactic("Left-hand side of the conclusion is not the same as the left-hand side of the premise + (ψ ⇔ τ)_.")
      } else if (
        !K.isSameSet(botK.right + phi_psi, premiseSequent.right + phi_tau) &&
        !K.isSameSet(botK.right + phi_tau, premiseSequent.right + phi_psi)
      )
        proof.InvalidProofTactic("Right-hand side of the conclusion + φ(ψ_) is not the same as right-hand side of the premise + φ(τ_) (or with ψ_ and τ_ swapped).")
      else
        proof.ValidProofTactic(bot, Seq(K.RightSubstIff(botK, -1, equalsK, lambdaPhiK)), Seq(premise))
    }
        */
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  object InstSchema extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof
    )(map: Map[F.Variable[?], F.Expr[?]])(premise: proof.Fact): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise).underlying
      val mapK = map.map((v, e) => (v.underlying, e.underlying))
      val botK = K.substituteVariablesInSequent(premiseSequent, mapK)
      val res = proof.getSequent(premise).substituteUnsafe(map)
      proof.ValidProofTactic(res, Seq(K.InstSchema(botK, -1, mapK)), Seq(premise))
    }
  }
  object Subproof extends ProofTactic {
    def apply(using proof: Library#Proof)(statement: Option[F.Sequent])(iProof: proof.InnerProof) = {
      val bot: Option[F.Sequent] = statement
      val botK: Option[K.Sequent] = statement map (_.underlying)
      if (iProof.length == 0) throw (new UnimplementedProof(proof.owningTheorem))
      val scproof: K.SCProof = iProof.toSCProof
      val premises: Seq[proof.Fact] = iProof.getImports.map(of => of._1)
      val judgement: proof.ProofTacticJudgement = {
        if (botK.isEmpty)
          proof.ValidProofTactic(iProof.mostRecentStep.bot, scproof.steps, premises)
        else if (!K.isSameSequent(botK.get, scproof.conclusion))
          proof.InvalidProofTactic(
            s"The subproof does not prove the desired conclusion.\n\tExpected: ${botK.get.repr}\n\tObtained: ${scproof.conclusion.repr}"
          )
        else
          proof.ValidProofTactic(bot.get, scproof.steps :+ K.Restate(botK.get, scproof.length - 1), premises)
      }
      judgement
    }
  }
*/
  class SUBPROOF(using val proof: Library#Proof)(statement: Option[F.Sequent])(val iProof: proof.InnerProof) extends ProofTactic {
    val bot: Option[F.Sequent] = statement
    val botK: Option[K.Sequent] = statement map (_.underlying)
    if (iProof.length == 0)
      throw (new UnimplementedProof(proof.owningTheorem))
    val scproof: K.SCProof = iProof.toSCProof

    val premises: Seq[proof.Fact] = iProof.getImports.map(of => of._1)
    def judgement: proof.ProofTacticJudgement = {
      if (botK.isEmpty)
        proof.ValidProofTactic(iProof.mostRecentStep.bot, scproof.steps, premises)
      else if (!K.isSameSequent(botK.get, scproof.conclusion))
        proof.InvalidProofTactic(s"The subproof does not prove the desired conclusion.\n\tExpected: ${botK.get.repr}\n\tObtained: ${scproof.conclusion.repr}")
      else
        proof.ValidProofTactic(bot.get, scproof.steps :+ K.Restate(botK.get, scproof.length - 1), premises)
    }
  }

  // TODO make specific support for subproofs written inside tactics.kkkkkkk

  inline def TacticSubproof(using proof: Library#Proof)(inline computeProof: proof.InnerProof ?=> Unit): proof.ProofTacticJudgement =
    val iProof: proof.InnerProof = new proof.InnerProof(None)
    computeProof(using iProof)
    SUBPROOF(using proof)(None)(iProof).judgement.asInstanceOf[proof.ProofTacticJudgement]

  object Sorry extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      proof.ValidProofTactic(bot, Seq(K.Sorry(bot.underlying)), Seq())
    }
  }

}
