package lisa.hol
import lisa.utils.fol.FOL as F
import F.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.{*, given}
import lisa.maths.SetTheory.Types.TypingRules.{BetaReduction}
import lisa.utils.prooflib.BasicStepTactic.{TacticSubproof => _, *}
import lisa.utils.prooflib.SimpleDeducedSteps.* 
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.automation.*
import lisa.automation.Substitution.{Apply as Substitute}

import lisa.maths.SetTheory.Functions.Function.{app, abs}
import lisa.maths.SetTheory.Functions.BasicTheorems.{absBodyEq, functionalExtentionality, funcBetweenEqInFuncSpace}
import lisa.maths.SetTheory.Base.Singleton
import Singleton.singleton

import lisa.hol.VarsAndFunctions.{computeType, contextToMap, tforall, TypedForall, HOLProofType, holeq, HOLSequent, =:=, TypeNonEmptyProof, TypedVariable,
          given_Conversion_TypedForall_Expr, given_Conversion_Expr_HOLSequent,
          given_Conversion_Expr_Expr, termToSetConv, setTermToSetConv}
import lisa.utils.prooflib.BasicStepTactic.*

import HOLHelperTheorems.{Bool, `0 : 𝔹`, `1 : 𝔹`, Zero, One, zero_in_B, =:=, nonEmptyTypeExists}


/**
  * Here we define and implement all the basic steps from HOL Light
  */
object HOLSteps extends lisa._HOL {
  import lisa.SetTheoryLibrary.{*, given}

  // Helper to extract typing context from a sequent
  @deprecated
  def extractContext(s: F.Sequent): Map[Variable[Ind], Typ] = ???

  //draft()
  
  //REFL
  //_TRANS
  //MK_COMB
  //ABS
  //BETA
  //ETA
  //ASSUME
  //_EQ_MP
  //DEDUCT_ANTISYM_RULE
  //INST
  //INST_TYPE

  private val A = typevar
  private val B = typevar
  private val t, u = variable[Ind >>: Ind]
  // Helpers for instantiating library theorems (some are stated using these names).
  private val Gf, Hf = variable[Ind >>: Ind]
  private val v = typedvar(B)
  private val w = typedvar(A)
  private val x = typedvar(A)
  private val y = typedvar(A)
  private val z = typedvar(A)
  private val e = typedvar(A ->: A)
  private val f = typedvar(A ->: B)
  private val g = typedvar(A ->: B)
  private val h = typedvar(B ->: A)

  private val p = typedvar(𝔹)
  private val q = typedvar(𝔹)
  private val r = typedvar(𝔹)

  val eqDefin = {
    val x = typedvar(A)
    val y = typedvar(A)
    val eqDefin = Axiom(((x::A) /\ (y::A)) ==> ((x =:= y)===One) <=> (x===y))
    eqDefin
  }



  val eqCorrect = Theorem((x::A, y::A) |- ((x =:= y)===One) <=> (x===y)) {
    have(thesis) by Restate.from(eqDefin)
  }


  val eqRefl = Theorem((x::A) |- (x =:= x)) {
    have(x::A |- (x === x)) by Restate
    thenHave((x::A) |- (x =:= x)) by Substitute(eqCorrect of (HOLSteps.y := x))

  }

  val eqTrans = Theorem( ((x::A), (y::A), (z::A), (x =:= y),  (y =:= z))  |- (x =:= z) )  {
    have((x::A, y::A, z::A, x === y, y === z)|- (x === y)) by Restate
    thenHave((x::A, y::A, z::A, x === y, y === z)|- (x === z)) by Substitute(y === z)
    thenHave(((x::A, y::A, z::A, eqOne(x =:= y), y === z)|- (x === z))) by Substitute(eqCorrect)
    thenHave(((x::A, y::A, z::A, eqOne(x =:= y), eqOne(y =:= z))|- (x === z))) by Substitute(eqCorrect of (x := y, y := z))
    thenHave(((x::A, y::A, z::A, eqOne(x =:= y), eqOne(y =:= z))|- eqOne(x =:= z))) by Substitute(eqCorrect of (y := z))
  }


  val eqSym = Theorem( ((x::A), (y::A), (x =:= y)) |- (y =:= x) )  {
    have(thesis) by Tautology.from(
      eqCorrect,
      eqCorrect of (HOLSteps.x := y, HOLSteps.y := x)
    )
  }

  val funcUnique = Theorem((f :: (A ->: B), g :: (A ->: B), x :: A, tforall(x :: A, f*x === g*x)) |- (f === g)) {
    assume(f :: (A ->: B))
    assume(g :: (A ->: B))
    assume(tforall(x :: A, f*x === g*x))

    val fIn = have(f ∈ (A ->: B)) by Hypothesis
    val gIn = have(g ∈ (A ->: B)) by Hypothesis

    val fBetween = have(functionBetween(f)(A)(B)) by Tautology.from(
      funcBetweenEqInFuncSpace of (lisa.maths.SetTheory.Base.Predef.f := f, A := A, B := B),
      fIn
    )
    val gBetween = have(functionBetween(g)(A)(B)) by Tautology.from(
      funcBetweenEqInFuncSpace of (lisa.maths.SetTheory.Base.Predef.f := g, A := A, B := B),
      gIn
    )

    val pointwise = have(forall(x, (x ∈ A) ==> (f*x === g*x))) by Hypothesis
    val conj = have(functionBetween(f)(A)(B) /\ functionBetween(g)(A)(B) /\ forall(x, (x ∈ A) ==> (f*x === g*x))) by Tautology.from(
      fBetween,
      gBetween,
      pointwise
    )

    have(thesis) by Tautology.from(
      functionalExtentionality of (lisa.maths.SetTheory.Base.Predef.f := f, g := g, A := A, B := B),
      conj
    )
  }
  val funcUnique2 =  Lemma((f :: (A ->: B), g :: (A ->: B), x :: A, tforall(x :: A, f*x === g*x)) |- ((f =:= g) === One)) {
    have(thesis) by Substitute(eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := (A ->: B)))(funcUnique)
  }

  val Bdef = Theorem((p ∈ 𝔹) |- ((p === Zero) \/ (p === One))) {
    val s1 = have    ((p ∈ unorderedPair(∅, singleton(∅))) |- ((p === ∅ )\/ (p === singleton(∅)))) by Weakening(pairAxiom of (z := p, x := ∅ , y := singleton(∅)))
    val s2 = have((p ∈ 𝔹) |- ((p === ∅) \/ (p === singleton(∅)))) by Substitute(𝔹.definition)(s1)
    val s3 = have((p ∈ 𝔹) |- ((p === Zero) \/ (p === singleton(∅)))) by Substitute(Zero.definition)(s2)
    have((p ∈ 𝔹) |- ((p === Zero) \/ (p === One))) by Substitute(One.definition)(s3)
  }


  val propExt = Theorem((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (p === q)) {

    val h2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (p === One)) by Restate
    val h3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (q === One)) by Restate
    val h4 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (p === q)) by Substitute(h3)(h2)

    val neq = have ((p === Zero, p === One )|- ()) subproof {
      val zeq = have(∅ === Zero) by Weakening(Zero.definition)
      val oeq = have(singleton(∅) === One) by Weakening(One.definition)
      have(∅ ∈ singleton(∅)) by Weakening(Singleton.membership of(y := ∅, x:= ∅))
      have((∅ === singleton(∅)) |- ()) by Restate.from(Singleton.nonEmpty of (x:= ∅))

      thenHave ((p === singleton(∅), p === ∅) |- ()) by Substitute(p === ∅)
      thenHave ((p === singleton(∅), p === Zero) |- ()) by Substitute(zeq)
      thenHave ((p === One, p === Zero) |- ()) by Substitute(oeq)
    }
    val i1 = have((p :: 𝔹  |- (!(p === One)) <=> (p === Zero))) by Tautology.from(Bdef of ( p:= p), neq)
    val i2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- !(q === One) <=> !(p === One)) by Tautology
    val i3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (q === Zero) <=> (p === Zero)) by Tautology.from(i2, i1, i1 of (p:=q))

    val j2 = have    ((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- p === Zero) by Tautology.from(Bdef of (p := p))
    val j3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- q === Zero) by Tautology.from(lastStep)
    val j4 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- (p === q)) by Substitute(j3)(j2)

    have(thesis) by Tautology.from(j4, i3, h4)

  }

    
  val absTHM = Theorem(
    (tforall(x :: A, t(x)::B), tforall(x :: A, u(x)::B), tforall(x :: A, holeq(B)*(t(x))*(u(x)) === One)) |- 
    (holeq(A ->: B)*(abs(A)(t))*(abs(A)(u)) === One)
  ) {
    val aT = assume(tforall(x :: A, t(x)::B))
    val aU = assume(tforall(x :: A, u(x)::B))
    val aEq = assume(tforall(x :: A, holeq(B)*(t(x))*(u(x)) === One))

    val pointwiseEq = have(forall(x, (x ∈ A) ==> (t(x) === u(x)))) subproof {
      val holeqTyped = have((x ∈ A, t(x) ∈ B, u(x) ∈ B) |- holeq(B)*(t(x))*(u(x)) === One) by Tautology.from(aEq of x)
      val eqTyped = thenHave((x ∈ A, t(x) ∈ B, u(x) ∈ B) |- (t(x) === u(x))) by Substitute(
        eqCorrect of (HOLSteps.x := t(x), HOLSteps.y := u(x), A := B)
      )
      have(x ∈ A ==> (t(x) === u(x))) by Tautology.from(eqTyped, aT of x, aU of x)
      thenHave(thesis) by RightForall
    }

    val absEq = have(abs(A)(t) === abs(A)(u)) by Tautology.from(
      absBodyEq of (Gf := t, Hf := u),
      pointwiseEq
    )

    // Explicit instantiation keys for TypingRules.TAbs (its schematic variables are named T1, T2, e).
    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]
    have(thesis) by Tautology.from(
      eqCorrect of (HOLSteps.x := abs(A)(t), HOLSteps.y := abs(A)(u), A := (A ->: B)),
      absEq,
      lisa.maths.SetTheory.Types.TypingRules.TAbs of (T1 := A, T2 := λ(x, B), e := t),
      lisa.maths.SetTheory.Types.TypingRules.TAbs of (T1 := A, T2 := λ(x, B), e := u)
    )
  }

  val betaConv = Theorem(((x :: A), tforall(x :: A, t(x)::B))|- holeq(B)*(abs(A)(t) * x) *t(x)) {
    val T, e2 = variable[Ind]
    val e = variable[Ind >>: Ind]
    assume(tforall(x :: A, t(x)::B))
    val txb = have(x :: A |- t(x)::B) by Restate.from(lastStep of x)

    val betaEq = have(x :: A |- abs(A)(t) * x === t(x)) by Tautology.from(BetaReduction of (T := A, e := t, e2 := x))
    val absTyped = have(x :: A |- (abs(A)(t) * x) :: B) by Congruence.from(txb, BetaReduction of (T := A, e := t, e2 := x))

    have(thesis) by Tautology.from(
      txb,
      absTyped,
      betaEq,
      eqCorrect of (HOLSteps.x := abs(A)(t) * x, HOLSteps.y := t(x), A := B)
    )
  }

  val etaConvEq = Theorem((f :: (A ->: B), x :: A) |- (abs(A)(λ(x, f*x)) === f)) {
    val lam = λ(x, f*x)
    assume(f :: (A ->: B))
    
    val pointwise = have(tforall(x :: A, abs(A)(lam)*x === f*x)) subproof {
      val T, e2 = variable[Ind]
      val e = variable[Ind >>: Ind]
      
      have((x :: A) ==> (abs(A)(lam)*x === f*x)) subproof {
        assume(x :: A)
        val betaEq = have(abs(A)(lam)*x === lam(x)) by Tautology.from(
          BetaReduction of (T := A, e := lam, e2 := x)
        )
        val lamApp = have(lam(x) === f*x) by Restate
        have(abs(A)(lam)*x === f*x) by Tautology.from(betaEq, lamApp)
      }
      thenHave(thesis) by RightForall
    }
    
    // Type abs(A)(lam) using TAbs
    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]
    
    val lamTyping = have(tforall(x :: A, lam(x) :: B)) subproof {
      // Need schematic variables matching TApp's names
      val e1, e2 = variable[Ind]
      val T1 = variable[Ind]
      val T2 = variable[Ind >>: Ind]
      
      have((x :: A) ==> (lam(x) :: B)) subproof {
        assume(x :: A)
        val lamApp = have(lam(x) === f*x) by Restate
        val fxTyped = have(f*x :: B) by Tautology.from(
          lisa.maths.SetTheory.Types.TypingRules.TApp of (e1 := f, e2 := x, T1 := A, T2 := λ(y, B))
        )
        have(thesis) by Congruence.from(fxTyped, lamApp)
      }
      thenHave(thesis) by RightForall
    }
    
    val absTyped = have(abs(A)(lam) :: (A ->: B)) by Tautology.from(
      lisa.maths.SetTheory.Types.TypingRules.TAbs of (T1 := A, T2 := λ(x, B), e := lam),
      lamTyping
    )
    val fTyped = have(f :: (A ->: B)) by Hypothesis
    
    have(thesis) by Tautology.from(
      funcUnique of (f := abs(A)(lam), g := f, A := A, B := B),
      absTyped,
      fTyped,
      pointwise
    )
  }

  // TODO: This theorem proof needs to be fixed - there's a subtle variable scoping issue
  // with the lambda binding and the schematic variable x in the theorem statement
  val etaConv = Theorem((f :: (A ->: B), x :: A) |- holeq(A ->: B) * (fun(x :: A, f*x)) * f) {
    have(thesis) by Sorry
  }

    val mk_comTHM = Theorem((f::( A ->: B), g::(A ->: B), x::A, y::A, f =:= g, x =:= y) |- (f*x =:= g*y)) {
    val typ1 = A ->: B
    val typ2 = A
    val vx = typedvar(A)
    val vf = typedvar(A ->: B)
    assume(f::(A ->: B))
    assume(g::(A ->: B))
    assume(x::A)
    assume(y::A)
    assume(f =:= g)
    assume(x =:= y)
    val p0 = have(HOLProofType(f*x)) 
    val p1 = have(f*x :: B |- f*x =:= f*x) by Tautology.from(eqRefl of (HOLSteps.x := f*x, A := B))
    val s1 = have(f*x =:= f*x) by Cut(p0, p1)
    val s2 = have((f :: typ1, g::typ1) |- (f===g)) by Tautology.from(eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := typ1))
    val s3 = have((x :: typ2, y::typ2) |- (x===y)) by Tautology.from(eqCorrect of (HOLSteps.x := x, HOLSteps.y := y, A := typ2))

    val s4 = have((x :: typ2, f::typ1, x === y) |- (f*x =:= f*y) === One) by RightSubstEq.withParameters(List((x, y)), (Seq(vx), f*x =:= f*vx))(s1)
    val s5 = have(((x :: typ2, f::typ1, x === y, f === g)) |- (f*x =:= g*y) === One) by RightSubstEq.withParameters(List((f, g)), (Seq(vf), f*x =:= vf*y))(s4)

    val s6 = have((x :: typ2, y::typ2, f::typ1, (f === g)) |- (f*x =:= g*y) === One) by Cut(s3, s5)
    val s7 = have((x :: typ2, y::typ2, f :: typ1, g::typ1) |- (f*x =:= g*y) === One) by Cut(s2, s6)
  }



  /**
   *  ------------------
   *     |- t = t
   */
  object REFL extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{
      // Extract typing context from current proof assumptions
      val pp = HOLProofType(t)
      val s1 = have(pp) //t::A
      val typ = s1.statement.right.head match
        case _ ∈ typ => typ
        case _ => return proof.InvalidProofTactic(s"Could not compute type of $t")
      have(Discharge(s1)(eqRefl of (x := t, A := typ)))
      have(Clean.all(lastStep))
    }
  }
  
  /**
   *  |- s = t    |- t = u
   *  ---------------------
   *        |- s = u
   */
  object _TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val s1 = t1.statement
      val s2 = t2.statement
      (s1, s2) match {
        case (HOLSequent(left1, *(*(=:= #@ (aa), s),ta)), HOLSequent(left2, (=:= #@ (ab))*tb*u) ) => //equality is too strict
          if isSame(ta, tb) then
            if isSame(aa, ab) then
              (s1.left ++ s2.left).foreach(assume(_))
              val p0 = have(s1) by Weakening(t1)
              val r0 = have(((s :: aa), (ta :: aa), (u :: aa), (ta =:= u) === One) |- (s =:= u) === One) by Cut(p0, eqTrans of (x := s, y := ta, z := u, A := aa))
              val r1 = have(((s :: aa), (ta :: aa), (u :: aa)) |- (s =:= u) === One) by Cut(t2, r0)
              val r2 = have(Discharge(have(HOLProofType(s)))(r1))
              val r3 = have(Discharge(have(HOLProofType(ta)))(r2))
              val r4 = have(Discharge(have(HOLProofType(u)))(r3))
              have(Clean.all(r4))
            else 
              return proof.InvalidProofTactic(s"Types don't agree: $aa and $ab")
          else 
            return proof.InvalidProofTactic(s"Middle elements don't agree: $ta and $tb")

        case (HOLSequent(left1, right1), HOLSequent(left2, right2) ) => 
          return proof.InvalidProofTactic(s"The facts should have equalities")
        case _ => 
          s1 match 
            case HOLSequent(left1, right1) => 
              return proof.InvalidProofTactic(s"The second fact is not parsable as an HOL sequent")
            case _ =>
              return proof.InvalidProofTactic(s"The first fact is not parsable as an HOL sequent")
      }
    }
  }

  
/*

  /**
   * Apply transitivity of equality, but with alpha equivalence.
   */
  object TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = 
      val s1 = t1.statement
      val s2 = t2.statement

      (s1, s2) match {
        case (HOLSequent(left1, (=:= #@aa)*s*ta), HOLSequent(left2, (=:= #@ab)*tb*u) ) => //equality is too strict
            if aa == ab then
              if ta == tb then
                _TRANS(t1, t2)
              else
                // try to see if ta alpha_eq tb
                TacticSubproof:
                  val alpha = have(ALPHA_EQUIVALENCE(ta, tb))
                  val s1 = have(_TRANS(t1, alpha))
                  val s2 = have(_TRANS(s1, t2))
            else 
              return proof.InvalidProofTactic(s"Types don't agree: $aa and $ab")

        case (HOLSequent(left1, right1), HOLSequent(left2, right2) ) => 
          return proof.InvalidProofTactic(s"The facts should have equalities")
        case _ => 
          s1 match 
            case HOLSequent(left1, right1) => 
              return proof.InvalidProofTactic(s"The second fact is not parsable as an HOL sequent")
            case _ =>
              return proof.InvalidProofTactic(s"The first fact is not parsable as an HOL sequent")

      }
  }


  */



  /**
   *  |- f = g    |- x = y
   *  ---------------------
   *        |- f x = g y
   */
  object MK_COMB extends ProofTactic {
    def apply(using proof: Proof)(f1: proof.Fact, f2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof {
      val fg = f1.statement
      val xy = f2.statement
      (fg, xy) match {
        case (HOLSequent(left1, (=:= #@ typ1)*ff*gg), HOLSequent(left2, (=:= #@ typ2)*xx*yy) )  => //equality is too strict
        typ1 match {
          case ->:(`typ2`, b) => 
            (f1.statement.left ++ f2.statement.left).foreach(assume(_))
            val s1 = have((xx :: typ2, yy::typ2, ff :: typ1, gg::typ1, ff =:= gg, xx =:= yy) |- (ff*xx =:= gg*yy)) by Weakening(mk_comTHM of (f := ff, g := gg, x := xx, y := yy))
            val d1 = have( Discharge(f1)(lastStep) )
            val d2 = have( Discharge(f2)(d1) )
            val d3 = have( Discharge(have(HOLProofType(xx)))(d2) )
            val d4 = have( Discharge(have(HOLProofType(yy)))(d3) )
            val d5 = have( Discharge(have(HOLProofType(ff)))(d4) )
            val d6 = have( Discharge(have(HOLProofType(gg)))(d5) )
            have(Clean.all(lastStep))

          case _ => 
            return proof.InvalidProofTactic(s"Types don't agree: fun types are $typ1 and arg types are $typ2")
        }
        case _ => 
          return proof.InvalidProofTactic(s"The facts should be of the form f =:= g and x =:= y")
      }
    }
  }


  /**
    *     |- t =:= u
    * ---------------------
    *  |- λx. t =:= λx. u
    * 
    */
  object ABS extends ProofTactic {
    def apply(using proof: Proof)(x: Variable[Ind], xTyp: Typ)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = prem.statement
      s1 match {
        case HOLSequent(left, (=:= #@ typ1)*tt*uu) => 
          // Assume everything except the binding variable's type
          prem.statement.left.filterNot(isSame(_, x::xTyp)).foreach(assume(_))
          val lt = abs(xTyp)(λ(x, tt))
          val lu = abs(xTyp)(λ(x, uu))

          val xta = x :: xTyp
          
          // Extract context without x for typing proofs

          have((tforall(xta, tt::typ1), tforall(xta, uu::typ1)) |- (x :: xTyp) ==> (holeq(typ1)*(tt)*(uu) === One)) by Weakening(prem)
          val h1 = thenHave((tforall(xta, tt::typ1), tforall(xta, uu::typ1)) |- forall(x, (x :: xTyp) ==> (holeq(typ1)*(tt)*(uu) === One))) by RightForall
          have((tforall(xta, tt::typ1), tforall(xta, uu::typ1), tforall(xta, holeq(typ1)*(tt)*(uu) === One)) |- (holeq(xTyp ->: typ1)*lt*lu === One)) by Weakening(absTHM of (t := λ(x, tt), u := λ(x, uu), A := xTyp, B := typ1))
          val h2 = have( Discharge(h1)(lastStep))
          have(HOLProofType(tt))
          thenHave(lastStep.statement.left.filterNot(isSame(_, x::xTyp)) |- (x :: xTyp) ==> (tt::typ1)) by Weakening

          val h3 = thenHave(lastStep.statement.left |- tforall(xta, tt::typ1)) by RightForall
          have(HOLProofType(uu))
          thenHave(lastStep.statement.left.filterNot(isSame(_, x::xTyp)) |- (x :: xTyp) ==> (uu::typ1)) by Weakening
          val h4 = thenHave(lastStep.statement.left |- tforall(xta, uu::typ1)) by RightForall
          val h5 = have( h2.statement -<? (h3.statement.right.head) ++<< h3.statement) by Cut(h3, h2)
          val h6 = if h5.statement.left.exists(isSame(_, h4.statement.right.head)) then have( h5.statement -<? (h4.statement.right.head) ++<< h4.statement) by Cut(h4, h5) else h5
          have(Clean.all(h6))

        case _ => 
          return proof.InvalidProofTactic(s"The fact should be of the form t =:= u")
      }
    }
  }




  /**
   * BETA_CONV((λx. t) u) produces |- (λx. t) u =:= t[x := u] 
   */
  object BETA_CONV extends ProofTactic {
    def apply(using proof: Proof)(tin: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      tin match
        case Sabs(typ1, Abs(xx, tt))*(r: Expr[Ind]) => 
          // val betaConv = Theorem(((x :: A), tforall(x :: A, t(x)::B))|- holeq(B)*(abs(A)(t) * x) *t(x))
          val typ2 = computeType(tin)
          val T = variable[Ind]
          val vx = xx
          val s1 = have((r :: typ1, tforall(vx :: typ1, tt::typ2)) |- (holeq(typ2)*(fun(vx :: typ1, tt) * r)*tt.substitute(vx := r))) by Weakening(betaConv of (A := typ1, B := typ2, t := λ(vx, tt), x := r))
          // Prove typing for tt: build tforall (may have free variable assumptions)
          val ttPre = have(HOLProofType(tt))
          val ttImp = have(ttPre.statement.left.filterNot(isSame(_, vx::typ1)) |- (vx :: typ1) ==> (tt::typ2)) by Weakening(ttPre)
          val ttypForall = have(ttImp.statement.left |- tforall(vx :: typ1, tt::typ2)) by RightForall(ttImp)
          val h1 = have( Discharge(ttypForall)(s1) )
          val h2 = have( Discharge(have(HOLProofType(r)))(h1) )
          have(Clean.all(h2))
        case _ => 
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) v")  
    }
  }

  /**
   * BETA((λx. t) x) produces |- (λx. t) x =:= t 
   */
  object BETA extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{
      t match
        case Sabs(typ1, tt)*(r: Variable[Ind]) => 
          // assure the right shape is present, and pass to the general case
          have(BETA_CONV(t))
        case _ => 
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) y")  

    }
  }

  /*
  object BETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      t match
        case (l:Abstraction)*(r: TypedVar) if l.bound == r => 
          val b = l.BETA
          val s1 = have(b.statement) by Weakening(b) //l*r =:= l.body
          val ctx = computeContext(Set(l*r, l.body))
          ctx._1.foreach(a => assume(a))
          ctx._2.foreach(a => assume(a))
          val bt = have((r::r.typ) |- ((l*r =:= l.body) === One)) by Restate.from(s1)
          val ptlr = have(HOLProofType(l*r))
          val ptlb = have(HOLProofType(l.body))
          val bth = have((r::r.typ, l*r :: l.defin.outType, l.body :: l.defin.outType) |- (l*r === l.body)) by Substitute(
            eqCorrect of (HOLSteps.x := l*r, HOLSteps.y := l.body, A := l.defin.outType)
          )(bt)
          have(Discharge(ptlr)(lastStep))
          have(Discharge(ptlb)(lastStep))
        case _ => 
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) x")
    }
  }


  // λ(x, t*x) === t
  object ETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar, t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      if t.freeVariables.contains(x) then
      return proof.InvalidProofTactic(s"Variable $x is free in the Expr[Ind] $t")
      val lxtx = λ(x, t*x)
      val ctx = computeContext(Set(lxtx, t))
      ctx._1.foreach(a => assume(a))
      ctx._2.foreach(a => assume(a))
      have(BETA_PRIM(lxtx*x))
      thenHave((x :: x.typ) ==> (lxtx*x === t*x)) by Restate.from
      thenHave(tforall(x, lxtx*x === t*x)) by RightForall
      val r1 = have((lxtx:: lxtx.typ, t::lxtx.typ) |- (lxtx === t)) by Tautology.from(
        funcUnique of (f := lxtx, g := t, A := x.typ, B := lxtx.defin.outType),
        lastStep
      )
      val r2 = have((t::lxtx.typ) |- (lxtx === t)) by Cut(have(HOLProofType(lxtx)), r1)
      have((lxtx === t)) by Cut(have(HOLProofType(t)), r2)
    }
  }

  */

  // λ(x, t*x) =:= t
  object ETA extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVariable, t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      
      if t.freeVars.contains(x) then
      return proof.InvalidProofTactic(s"Variable $x is free in the Expr[Ind] $t")
      val lxtx = λ(x, t*x)
      val ttype_step = have(HOLProofType(t))
      val restype = computeType(t*x)
      val ttype = x.typ ->: restype
      val s1 = have((t :: ttype, x :: x.typ) |- holeq(ttype) * (fun(x :: x.typ, t*x)) * t) by Weakening(etaConv of (HOLSteps.x := x, f := t, A := x.typ, B := restype))
      have(Discharge(ttype_step)(s1))
      have(Clean.all(lastStep))
    }
  }

  

  /**
    * ---------------
    *     t |- t
    */
  object ASSUME extends ProofTactic {
    def apply(using proof: Proof)(t:Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      val typ = computeType(t)
      if typ == 𝔹 then
        have(t |- t) by Restate
        have(Clean.all(lastStep))
      else
        return proof.InvalidProofTactic(s"Expr[Ind] $t is not a boolean")
    }

  }


  /**
    *  |- t = u    |- t
    * -------------------
    *       |- u
    */
  object EQ_MP extends ProofTactic {
    def apply(using proof: Proof)(eq: proof.Fact, p: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      if eq.statement.right.size != 1 then
        return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One")
      eq.statement match
        case HOLSequent(left, ((=:= #@ `𝔹`)*t*u)) => 
          if p.statement.right.size != 1 then
            return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
          p.statement.right.head match
            case eqOne(`t`) =>
              val assumptions = eq.statement.left ++ p.statement.left
              val vt = variable[Ind]
              val hp = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- p.statement.right) by Weakening(p)
              val h1 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- t === u) by Tautology.from(eqCorrect of (x := t, y := u, A := 𝔹), eq)
              val hc = have((assumptions + (t :: 𝔹) + (u :: 𝔹) + (t === u)) |- (u === One)) by RightSubstEq.withParameters(List((t, u)), (Seq(vt), vt === One))(hp)
              val h2 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- (u === One)) by Cut(h1, hc)
              val pt = have(HOLProofType(t))
              val h3 = have(Discharge(pt)(h2))
              val h4 = have(Discharge(have(HOLProofType(u)))(h3))
              have(Clean.all(h4))
    
            case _ =>
              return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
        case _ =>
          return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One ")
          
    }

  }


  /**
    *      A |- p   B |- q
    * -------------------------
    *   A - p, B - q |- p = q
    */
  object DEDUCT_ANTISYM_RULE extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      if t1.statement.right.size != 1 || t2.statement.right.size != 1 then
        return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
      val left1 = t1.statement.left
      val c1 = t1.statement.right.head
      val left2 = t2.statement.left
      val c2 = t2.statement.right.head
      (c1, c2) match 
        case (eqOne(p), eqOne(q)) =>
          ((left1 - c2) ++ (left2 - c1)).foreach(assume(_))
          val qp = have((p :: 𝔹, q :: 𝔹) |- (q === One) ==> (p === One)) by Weakening(t1)
          val pq = have((p :: 𝔹, q :: 𝔹) |- (p === One) ==> (q === One)) by Weakening(t2)
          val pivot = have((p :: 𝔹, q :: 𝔹) |- (q === One) <=> (p === One)) by RightAnd(pq, qp)
          val h0 = have((p :: 𝔹, q :: 𝔹) |- (p === q)) by Cut.withParameters((q === One) <=> (p === One))(pivot, propExt of (HOLSteps.p -> p, HOLSteps.q -> q))
          val h1 = have((p :: 𝔹, q :: 𝔹, p === q) |- (p =:= q === One)) by Weakening(eqCorrect of (A -> 𝔹, x -> p, y -> q))
          val h2 = have((p :: 𝔹, q :: 𝔹) |- (p =:= q === One)) by Cut(h0, h1)
          val h3 = have(Discharge(have(HOLProofType(p)))(h2))
          val h4 = have(Discharge(have(HOLProofType(q)))(h3))
          have(Clean.all(h4))

        
        case _ =>
          return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
    }

  }

  object INST extends ProofTactic {
    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val k = prem.of(inst.map(_ := _)*)
      val h0 = have(k.statement) by Restate.from(k)
      val fv = prem.statement.freeVars 
      val violating = inst.collectFirst {
        case (v: TypedVariable, t) if fv.contains(v) && (v.asInstanceOf[TypedVariable].typ != computeType(t)) => (v, t)
      }
      violating match
        case Some((v, t)) => return proof.InvalidProofTactic(s"Type mismatch in instantiation: ${v} has type ${v.typ} but term ${t} has type ${computeType(t)}")
        case None => ()
      val instWithProofs = inst.flatMap((v, t) => 
        if !fv.contains(v) then
          None // no need to discharge if the variable isn't free in the statement
        else 
          val typProof = have(HOLProofType(t))
          Some((v, t, typProof))
      )
      instWithProofs.foldLeft(h0:ip.Fact) {
        case (h, (v, t, typProof)) =>
          println(s"Discharging ${t} with proof ${typProof.statement}")
          have(Discharge(typProof)(h))
      }
      println(s"Final statement after instantiation: ${lastStep.statement}")
      have(Clean.all(lastStep))
      println(s"Final statement after cleaning     : ${lastStep.statement}")
    }  
  }



  object INST_TYPE extends ProofTactic {

    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      val fv = prem.statement.freeVars
      
      val instWithProofs = inst.flatMap((v, t) => 
        if !fv.contains(v) then
          None // no need to discharge if the variable isn't free in the statement
        else 
          val typProof = have(TypeNonEmptyProof(t))
          Some((v, t, typProof))
      )
      val k = prem.of(inst.map(_ := _)*)
      val h0 = have(k.statement) by Restate.from(k)
      have(Clean.all(h0))
    }

  }
/*
  object SYM extends ProofTactic {
    def apply(using proof: Proof)(p: proof.Fact): proof.ProofTacticJudgement = TacticSubproof {
      val stmt = p.statement
      stmt match
        case HOLSequent(left, (=:= #@ typ)*s*t) =>
          // flip
          val s0 = have((stmt.left + (s :: typ) + (t :: typ)) |- (s =:= t) === One) by Weakening(p)
          val s1 = have((stmt.left + (s :: typ) + (t :: typ)) |- (t =:= s) === One) by Cut(s0, eqSym of (x := s, y := t, A -> typ))
          val s2 = have(Discharge(have(HOLProofType(s)))(s1))
          val s3 = have(Discharge(have(HOLProofType(s)))(s2))
        case _ => return proof.InvalidProofTactic(s"Sequent must contain an equality s =:= t to flip.")
    }
  }

  /**
   * Apply equality transitivity, but flip the equalities if necessary.
   * 
   * @see [[_TRANS]]
   */
  object _TRANS_SYM extends ProofTactic {
    def apply(using proof: Proof)(p1: proof.Fact, p2: proof.Fact): proof.ProofTacticJudgement =
      val s1 = p1.statement
      val s2 = p2.statement
      (s1, s2) match
        case (HOLSequent(left1, (=:= #@ aa)*s*ta), HOLSequent(left2, (=:= #@ ab)*tb*u) ) => //equality is too strict
          if aa == ab then
            // fine as is?
            if ta == tb then
              _TRANS(p1, p2)
            // flip first?
            else if s == tb then
              _TRANS(have(SYM(p1)), p2)
            // flip second?
            else if u == ta then
              _TRANS(p1, have(SYM(p2)))
            // flip both?
            else if u == s then
              _TRANS(have(SYM(p1)), have(SYM(p2)))
            else
              proof.InvalidProofTactic(s"Could not construct an instance of transitivity from Expr[Ind]s: \n\t$s\n\t$ta\n\t$tb\n\t$u")
          else 
            proof.InvalidProofTactic(s"Types don't agree: $aa and $ab")

        case (HOLSequent(left1, right1), HOLSequent(left2, right2) ) => 
          proof.InvalidProofTactic(s"The facts should have equalities")
        case _ => 
          s1 match 
            case HOLSequent(left1, right1) => 
              proof.InvalidProofTactic(s"The second fact is not parsable as an HOL sequent")
            case _ =>
              proof.InvalidProofTactic(s"The first fact is not parsable as an HOL sequent")
  }

  /**
   * |- λx. t = λy. t[x := y] if y is not free in t
   * 
   */
  private object _ALPHA_CONV extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind], x: Variable[Ind], xTyp: Typ, y: Variable[Ind], yTyp: Typ): proof.ProofTacticJudgement = TacticSubproof {
      if !t.freeVariables.contains(y) then
        val ld = λ(x, t)
        if x == y then
          // trivial
          have(REFL(ld))
        else
          val s0 = have(BETA((ld * x)))               // |- (λx. t) x =:= t
          val s1 = have(INST(Seq(x -> y), s0))        // |- (λx. t) y =:= t[x := y]
          val s2 = have(ABS(y, yTyp)(s1))                   // |- (λy. (λx. t) y) =:= λy. t[x := y]
          val s3 = have(ETA(y, yTyp, ld))                   // |- (λy. (λx. t) y) =:= (λx. t)
          val s4 = have(_TRANS_SYM(s2, s3))           // |- (λx. t) =:= λy. t[x := y]
      else
        return proof.InvalidProofTactic(s"Not applicable: the variable $y is free in the Expr[Ind] $t.")
    }
  }

  /**
   * Recursively replace every bound x by y in t.
   * 
   * Will not behave nicely on non-HOL Expr[Ind]s.
   */
  private object _ALPHA_CONV_REC extends ProofTactic {
    var debug = false
    def apply(using proof: Proof)(t: Expr[Ind], x: Variable[Ind], y: Variable[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      t match
        case Sabs(typ, Abs(v, body)) if v == x =>
          val xTyp = typ  // Type of x
          val i0 = have(_ALPHA_CONV(body, x, xTyp, y, xTyp))      // |- λx. t = λy. t[x := y]
          val i1 = have(_ALPHA_CONV_REC(body, x, y))  // |- t = t.rec(x -> y)
          val i2 = have(INST(Seq(x -> y), i1))            // |- t[x := y] = t.rec(x -> y)[x := y]
          val i3 = have(ABS(y, xTyp)(i2))                       // |- λy. t[x := y] = λy. t.rec(x -> y)[x := y]
          have(_TRANS_SYM(i0, i3))
        case Sabs(typ, Abs(v, body)) =>
          val inner = have(_ALPHA_CONV_REC(body, x, y)) // |- t = t.rec(x -> y)
          have(ABS(v, typ)(inner))                             // |- λx. t = λx. t.rec(x -> y)
        case App(App(`app`, func), arg) =>
          val fconv = have(_ALPHA_CONV_REC(func, x, y))     // |- func = func.rec(x -> y)
          val aconv = have(_ALPHA_CONV_REC(arg, x, y))      // |- arg = arg.rec(x -> y)
          have(MK_COMB(fconv, aconv))                       // |- func * arg = func.rec * arg.rec
        case _ => 
          have(REFL(t))                                     // |- t = t
    }
  }

  /**
   * Given two Expr[Ind]s, if they are alpha-equivalent, produce a proof of it, else fail.
   */
  object ALPHA_EQUIVALENCE extends ProofTactic {

    private val name = "alph"

    private def alphaEquivalent(t1: Expr[Ind], t2: Expr[Ind]): Boolean = 
      val res = t1 == t2 || {
        (t1, t2) match
          case (App(App(`app`, f1), a1), App(App(`app`, f2), a2)) =>
            alphaEquivalent(f1, a1) && alphaEquivalent(f2, a2)
          case (Sabs(typ1, Abs(v1, b1)), Sabs(typ2, Abs(v2, b2))) if typ1 == typ2 =>
            alphaEquivalent(b1.substitute(v1 := v2), b2)
          case _ => 
            t1 == t2
      }
      res


    private def alpha(using proof: Proof)(t1: Expr[Ind], t2: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      (t1, t2) match 
        case (App(App(`app`, f1), a1), App(App(`app`, f2), a2)) => // f * u, g * v
          val funs = have(ALPHA_EQUIVALENCE(f1, f2))  // |- f = g
          val args = have(ALPHA_EQUIVALENCE(a1, a2))    // |- u = v
          have(MK_COMB(funs, args))                             // |- f * u = g * v
        case (Sabs(typ1, Abs(v1, b1)), Sabs(typ2, Abs(v2, b2))) if typ1 == typ2 => // λx. t, λy. s
          val fresh = Variable.fresh[Ind]((t1.freeVariables ++ t2.freeVariables).toSet, name)
          val s1 = have(_ALPHA_CONV_REC(t1, v1, fresh))   // |- λx. t = λz. t[x := z]
          val s2 = have(_ALPHA_CONV_REC(t2, v2, fresh))   // |- λy. s = λz. s[y := z]
          val b1sub = b1.substitute(v1 := fresh)        // t[x := z]
          val b2sub = b2.substitute(v2 := fresh)        // s[y := z]
          val rb1 = reduceExpr[Ind](b1sub)        
          val rb2 = reduceExpr[Ind](b2sub)        
          val inner = have(ALPHA_EQUIVALENCE(rb1, rb2))           // |- t[x := z] = s[y := z]
          val abs = have(ABS(fresh, typ1)(inner))                     // |- λz. t[x := z] = λz. s[y := z]
          
          val s3_step = _TRANS(s1, abs)
          val s3 = have(s3_step)                        // |- λx. t = λz. s[y := z]
          val s4 = have(SYM(s2))                                // |- λz. s[y := z] = λy. s
          have(_TRANS(s3, s4))                                  // |- λx. t = λy. s
        case _ => 
          have(REFL(t1))                                        // |- t = t
    }

    def apply(using proof: Proof)(t1: Expr[Ind], t2: Expr[Ind]): proof.ProofTacticJudgement = 
      if alphaEquivalent(t1, t2) then
        alpha(t1, t2)
      else proof.InvalidProofTactic(s"Given Expr[Ind]s are not alpha equivalent: $t1 and $t2.")
  }

  /**
    * For a Expr[Ind] `r`, prove that `r === r2`, where `r2` is its canonical form,
    * with internal instantiations eliminated.
    *
    * For example, `DEF_RED((λf. f x) [x := y])` proves that 
    * `(λf. f x) [x := y] === λf. f y` . 
    *
    * Eliminates [[InstAbstraction]], [[TypeInstAbstractionWithout]], and
    * [[TypeInstAbstractionWith]]. Produces a trivial proof of `r === r` if the
    * Expr[Ind] is already canonical.
    */
  object DEF_RED extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      t match
        case tyaout: TypeInstAbstractionWithout => 
          ip.cleanAssumptions
          val baseDef = tyaout.base.defin.bodyProp
          val inst = tyaout.typeinst
          val instDef = baseDef.substitute(inst.map(_ := _.asInstanceOf).toSeq: _*) // force instantiation
          val (x, oldType, newType) = baseDef match
            case F.forall(xOld: F.Variable, F.==>(_ is (tp: Expr[Ind]), _)) => 
              val newType = tp.substituteUnsafe(inst)
              val x = TypedVar(xOld.id, newType)
              (x, tp, newType)
            case _ => 
              throw new Exception(s"Was expecting a definition of the form ∀(x: TypedVar,  x::T => f) but got $baseDef")

          
          instDef match
            case F.forall(_, F.==>(v2 is (tp2: Expr[Ind]), l === r)) =>
              assert(tp2 == newType, s"Malformed type instantiation. Expected $tp2 == $newType.")
              val defR = have(DEF_RED(r))
              defR.statement.right.head match
                case `r` === r2 => 
                  // r2 is the canonical form of r, so λ(x, r2) is the canonical form of t
                  val lambdaR = λ(x, r2)
                  val ctx = computeContext(Set(t, lambdaR))
                  val assumptions = ctx._1 ++ ctx._2 + instDef

                  val sv = F.Variable("@@substitutionVariable@@") // dummy substitution variable

                  // we also know that l = t * x
                  val a1 = have(instDef |- instDef) by Hypothesis
                  val s0 = have(assumptions + (x is newType) |- t*x === r) by Weakening(a1 of x)
                  val s1 = have(assumptions + (x is newType) + (r === r2) |- t*x === r2) by RightSubstEq.withParameters(List(r -> r2), F.lambda(sv, t*x === sv))(s0)
                  val s2 = have(assumptions + (x is newType) |- t*x === r2) by Cut(defR, s1)

                  // abstract away x
                  // λ(x, r) * x === r
                  val pure = have(BETA_PRIM(lambdaR*x)) // λ(x, r)*x === r
                  val s3 = have(assumptions + (x is newType) + (lambdaR*x === r2) |- t*x === lambdaR*x) by RightSubstEq.withParameters(List(r2 -> lambdaR*x), F.lambda(sv, t*x === sv))(s2)
                  val s4 = have(assumptions + (x is newType) |- t*x === lambdaR*x) by Cut(pure, s3)
                  val s5 = have(assumptions |- (x is newType) ==> (t*x === lambdaR*x)) by Restate.from(s4)
                  val s6 = have(assumptions |- tforall(x, t*x === lambdaR*x)) by RightForall(s5)

                  // eliminate x, t === lambdaR by functional extensionality
                  val newOutType = tyaout.base.defin.outType.substitute(inst.map(_ := _.asInstanceOf).toSeq: _*)
                  val absType = newType ->: newOutType
                  val funcExt = funcUnique of (f := lambdaR, g := t, A := newType, B := newOutType)
                  val s7 = have(assumptions + (t is absType) + (lambdaR is absType) |- (t === lambdaR)) by Tautology.from(funcExt, s6)

                  // remove extra assumptions and clean up
                  // val repr = tyaout.base.defin.reprVar
                  val s8 = have(Discharge(have(HOLProofType(t)))(s7))
                  val s9 = have(Discharge(have(HOLProofType(lambdaR)))(s8))
                case _ => 
                  throw new Exception(s"Was expecting an equality but got ${defR.statement.right.head}")

            case _ => 
              throw new Exception(s"Was expecting a definition of the form ∀(x: TypedVar,  x::T => f) but got $instDef")
          
        case tyawith: TypeInstAbstractionWith => 
          ip.cleanAssumptions
          val freeVars = tyawith.base.freeVars
          val inst = tyawith.typeinst
          val newTypes = freeVars.map(v => v.typ.substituteUnsafe(inst))
          val newVars = freeVars.zip(newTypes).map((v, t) => TypedVar(v.id, t))
          val bodyProp = tyawith.base.defin.bodyProp
          val baseStmt = have(Restate(bodyProp |- bodyProp)).of(inst.map(_ := _.asInstanceOf).toSeq: _*)
          val instStmt = newVars.foldLeft(baseStmt: ip.Fact) { case (step, v) =>
            val s0 = step of v
            s0.statement.right.head match
              case F.==>(left, right) =>
                val s1 = have(step.statement.left + (v :: v.typ) |- right) by Restate.from(s0)
                s1
              case _ =>
                throw new Exception(s"Malformed definition. Expected type qualified proposition (x :: T ==> P(x)) but got ${s0.statement.right.head}")
          }
          val instDef = instStmt.statement.right.head
          val (x, oldType, newType) = instDef match
            case F.forall(xOld: F.Variable, F.==>(_ is (tp: Expr[Ind]), _)) => 
              val newType = tp.substituteUnsafe(inst)
              val x = TypedVar(xOld.id, newType)
              (x, tp, newType)
            case _ => 
              throw new Exception(s"Was expecting a definition of the form ∀(x: TypedVar,  x::T => f) but got $instDef")
          
          instDef match
            case F.forall(_, F.==>(v2 is (tp2: Expr[Ind]), l === r)) =>
              assert(tp2 == newType, s"Malformed type instantiation. Expected $tp2 == $newType.")
              val defR = have(DEF_RED(r))
              defR.statement.right.head match
                case `r` === r2 => 
                  // r2 is the canonical form of r, so λ(x, r2) is the canonical form of t
                  val lambdaR = λ(x, r2)
                  val ctx = computeContext(Set(t, lambdaR))
                  val assumptions = ctx._1 ++ ctx._2 + instDef

                  val sv = F.Variable("@@substitutionVariable@@") // dummy substitution variable

                  // we also know that l = t * x
                  val a1 = have(instDef |- instDef) by Hypothesis
                  val s0 = have(assumptions + (x is newType) |- t*x === r) by Weakening(a1 of x)
                  val s1 = have(assumptions + (x is newType) + (r === r2) |- t*x === r2) by RightSubstEq.withParameters(List(r -> r2), F.lambda(sv, t*x === sv))(s0)
                  val s2 = have(assumptions + (x is newType) |- t*x === r2) by Cut(defR, s1)

                  // abstract away x
                  // λ(x, r) * x === r
                  val pure = have(BETA_PRIM(lambdaR*x)) // λ(x, r)*x === r
                  val s3 = have(assumptions + (x is newType) + (lambdaR*x === r2) |- t*x === lambdaR*x) by RightSubstEq.withParameters(List(r2 -> lambdaR*x), F.lambda(sv, t*x === sv))(s2)
                  val s4 = have(assumptions + (x is newType) |- t*x === lambdaR*x) by Cut(pure, s3)
                  val s5 = have(assumptions |- (x is newType) ==> (t*x === lambdaR*x)) by Restate.from(s4)
                  val s6 = have(assumptions |- tforall(x, t*x === lambdaR*x)) by RightForall(s5)

                  // eliminate x, t === lambdaR by functional extensionality
                  val newOutType = tyawith.base.defin.outType.substitute(inst.map(_ := _.asInstanceOf).toSeq: _*)
                  val absType = newType ->: newOutType
                  val funcExt = funcUnique of (f := lambdaR, g := t, A := newType, B := newOutType)
                  val s7 = have(assumptions + (t is absType) + (lambdaR is absType) |- (t === lambdaR)) by Tautology.from(funcExt, s6)

                  // remove extra assumptions and clean up
                  val s8 = have(Discharge(have(HOLProofType(t)))(s7))
                  val s9 = have(Discharge(have(HOLProofType(lambdaR)))(s8))

                  val defFold = have(Restate(tyawith.base.defin |- bodyProp))
                  val s10 = have(Discharge(defFold)(s9))
                case _ => 
                  throw new Exception(s"Was expecting an equality but got ${defR.statement.right.head}")

            case _ => 
              throw new Exception(s"Was expecting a definition of the form ∀(x: TypedVar,  x::T => f) but got $instDef")

        case ia: InstAbstraction => //  $λ*a*b*c...
          val base = ia.base
          val insts = ia.insts
          ip.cleanAssumptions
          val a1 = assume(base.defin.bodyProp)
          val eq = insts.foldRight(a1: ip.Fact)((inst, acc) =>
            val i1 = acc of inst
            i1.statement.right.head match
              case F.==>(left, right) =>  //   |- inst :: x.typ    --- not checking that type of insts match types freevars

                val i2 = have((i1.statement.left + left) |- right) by Restate.from(i1)
                val b1 = have(HOLProofType(inst._2))
                if b1.statement.right.head != left then
                  throw new Exception(s"Can't instantiate variable $left with Expr[Ind] ${inst} of type  ${b1.statement.right.head}.")
                val b2 = have(Discharge(b1)(i2))
                b2
              case _ =>
                throw new Exception(s"Was expecting an implication  while unfolfing instantiations, but got ${i1.statement.right.head}." +
                  s"\n The instantiation was $inst. \n The formula was ${a1.statement}." )
          )
          eq.statement.right.head match
            case F.forall(x2: F.Variable, F.==>(v is (tp: Expr[Ind]), l === r)) => //ia.repr*insts...*x = ir.repr.body
              val x = x2 match
                case x: TypedVar => x
                case _ => TypedVar(x2.id, tp)
              val def_red_r = have(DEF_RED(r)) // r === r2
              def_red_r.statement.right.head match
                case `r` === r2 => 
                  val lambdar = λ(x, r2)
                  val ctx = computeContext(Set(t, lambdar))
                  val assump = ctx._1 ++ ctx._2
                  val ctxlr = computeContext(Set(lambdar, r2))
                  val goal = have((assump + (x::x.typ)) |- (t*x === r)).by.bot
                  val i0 = have((assump + (x::x.typ)) |- (t*x === r)) by Weakening(eq of x)
                  val xx = F.Variable.fresh[F.Sequent](Seq(i0.statement, def_red_r.statement), "xx")
                  val i1 = have((assump + (x::x.typ) + (r === r2)) |- (t*x === r2)) by RightSubstEq.withParameters(List((r, r2)), F.lambda(xx, t*x === xx))(i0) 
                  val i2 = have(Discharge(def_red_r)(i1))
                  val h = have((assump + (x::x.typ) + (r2 === lambdar*x)) |- t*x === lambdar*x) by RightSubstEq.withParameters(List((r2, lambdar*x)), F.lambda(xx, t*x === xx))(i2) 
                  val pure = have(BETA_PRIM(lambdar*x)) // λ(x, r)*x === r
                  val h0 = have(Discharge(pure)(h))
                  thenHave(assump |- (x::x.typ ==> (t*x === lambdar*x))) by Restate.from
                  val resSeq = have(assump |- tforall(x, t*x === lambdar*x)).by.bot 
                  val h1 = thenHave(assump |- tforall(x, t*x === lambdar*x)) by RightForall
                  val iatyp = x.typ ->: base.defin.outType
                  val fu = funcUnique of (f := lambdar, g := t, A := x.typ, B := base.defin.outType)
                  val h2 = have((assump + (t :: iatyp) + (lambdar :: iatyp))  |- (t === lambdar)) by Tautology.from(
                    fu,
                    eq,
                    h1
                  )
                  val h3 = have(Discharge(have(HOLProofType(lambdar)))(h2))
                  val ptt = have(HOLProofType(t))
                  val h4 = have(Discharge(ptt)(h3))

                  val prop_bodyprop = have(Restate(base.defin |- base.defin.bodyProp))
                  val h5 = have(Discharge(prop_bodyprop)(h4))
                  
                case fail === _ => 
                  throw new Exception(s"Was expecting an equation with left hand side $r but got $fail")
                case fail => 
                  throw new Exception(s"Was expecting an equation as return of DEF_RED but got $fail")
            case F.forall(x: TypedVar, F.==>(tp, r)) =>
              throw new Exception("Was expecting something of the form ∀(x, x::T => l === r) but got" + eq.statement)
            case F.forall(x: TypedVar, r) =>
              throw new Exception("Was expecting something of the form ∀(x,  x::T => f) but got" + eq.statement)
            case F.forall(x: F.Variable, r) =>
              throw new Exception("Was expecting something of the form ∀(x:TypedVar,  x::T => f) but got" + eq.statement)
            case r => 
              throw new Exception(s"Was expecting a formula of the form ∀(x, f) but got $r")


        case abs: Abstraction => 
          have(abs === abs) by Restate
        case v: TypedVar => 
          have(v === v) by Restate
        case f*u =>
          val s1 = have(DEF_RED(f))
          val s2 = have(DEF_RED(u))
          (s1.statement.left ++ s2.statement.left).foreach(f => assume(f))
          (s1.statement.right.head, s2.statement.right.head) match
            case (`f` === f2, `u` === u2) =>
              val x = F.Variable.fresh(Seq(f, f2, u, u2), "x")
              val y = F.Variable.fresh(Seq(f, f2, u, u2), "y")
              //val y = typedvar(computeType(u))
              val s3 = have(f*u === f*u) by Restate
              val fu = f*u
              val f2u2 = f2*u2
              //val judg = RightSubstEq.withParameters(List(F.lambda(Seq(), f) -> F.lambda(Seq(), f2), F.lambda(Seq(), u) -> F.lambda(Seq(), u2)), (Seq(x, y), app(f, u) === app(x, y)))(s3)(have((f === f2, u === u2) |- fu === f2u2).by.bot)
              val s4 = have((f === f2, u === u2) |- fu === f2u2) by RightSubstEq.withParameters(List(F.lambda(Seq(), f) -> F.lambda(Seq(), f2), F.lambda(Seq(), u) -> F.lambda(Seq(), u2)), (Seq(x, y), fu === app(x, y)))(s3)
              val s5 = have((u === u2) |- f*u === f2u2) by Cut(s1, s4)
              val s6 = have(fu === f2u2) by Cut(s2, s5)
            case (fail1, fail2) =>
              throw new Exception(s"Was expecting two equations with left hand side $f but got $fail1 and with left hand side $u but got $fail2")
        case t => 
          have(t === t) by Restate

    }

    def THM(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      prem.statement.right.head match
        case eqOne(r) =>
          val def_red_r = have(DEF_RED(r)) // r === r2
          def_red_r.statement.right.head match {
            case `r` === r2 =>
              val left = prem.statement.left ++ def_red_r.statement.left
              val s0 = have((left) |- eqOne(r)) by Weakening(prem)
              val s1 = have((left + (r === r2)) |- eqOne(r2)) by RightSubstEq.withParameters(List(r -> r2), F.lambda(x, eqOne(x)))(s0)
              val s2 = have((left) |- eqOne(r2)) by Cut(def_red_r, s1)
              have(Clean.all(s2))
            case fail === _ =>
              throw new Exception(s"Was expecting an equation with left hand side $r but got $fail")
            case _ =>
              throw new Exception(s"Was expecting an equation as return of DEF_RED but got ${def_red_r.statement.right.head}")
          }

        case _ => 
          throw new Exception(s"Was expecting an r === One but got ${prem.statement.right.head}")
    
    }
  }

*/
  object Clean {

    def variable(using proof: Proof)(ta: TypeAssign[Variable[Ind]])(prem: proof.Fact) : proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val (v, typ) = (ta.vari, ta.typ)

      if (prem.statement -<< ta).freeVars.contains(v) then
        return proof.InvalidProofTactic(s"The variable ${v} is used in the sequent and it's type assignment can't be eliminated")
      println(s"Cleaning variable ${v} of type ${typ} from the sequent ${prem.statement}")
      val p1 = have(TypeNonEmptyProof(ta.typ))
      println(s"p1: ${p1.statement}")
      println(s"ta   : ${ta}")
      println(s"F.exists: ${F.exists(v, ta)}")
      println(s"res: ${prem.statement -<? ta +<? F.exists(v, ta)}")
      val p2 = have(prem.statement -<? ta +<? F.exists(v, ta)) by LeftExists.withParameters(ta, v)(prem)
      println(s"p2: ${p2.statement}")
      val p3 = have(Discharge(p1)(p2))
      println(s"p3: ${p3.statement}")
    }


    def allVariables(using proof: Proof)(prem:proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val statement = prem.statement
      val vars = statement.left.collectFirst[TypeAssign[Variable[Ind]]]{
        case f @ ((v:Variable[Ind] @unchecked) ∈ (typ:Expr[Ind])) if !(statement -<< f).freeVars.contains(v) => (v :: typ)
      }
      if vars.nonEmpty then
        val h = have(Clean.variable(vars.head)(prem))
        allVariables(h)
      else
        have(prem.statement) by Weakening(prem)
    }

    def typeVar(using proof: Proof)(net: Expr[Prop], tv: Variable[Ind])(prem: proof.Fact) : proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      println(s"net   : ${net}")
      println(s"tv    : ${tv}")
      println(s"prem  : ${prem.statement}")
      println(s"Nete  : ${nonEmptyTypeExists.statement}")
      println(s"Target: ${prem.statement -<? net +<< nonEmptyTypeExists.statement.right.head}")
      val p2 = have(prem.statement -<? net +<< nonEmptyTypeExists.statement.right.head) by LeftExists.withParameters(net, tv)(prem)
      val p3 = have(Discharge(nonEmptyTypeExists)(p2))
    }

    def allTypeVars(using proof: Proof)(prem:proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val statement = prem.statement
      val typ = statement.left.collectFirst({
        case f @ exists(x, y ∈ (tv: Variable[Ind])) if x == y && !(statement -<? f).freeVars.contains(tv) => (f, tv)
      })
      val size = typ.size
      typ match {
        case Some((f, tv)) =>
          val h = have(Clean.typeVar(f, tv)(prem))
          if h.statement.left.find({
            case exists(x, y ∈ (a: Variable[Ind])) if x == y => true
            case _ => false
          }) == f then
            throw new Exception (s"Could not eliminate type variable ${f} from the premise.")
          allTypeVars(h)
        case None =>
          have(prem.statement) by Weakening(prem)
      }
    }

    def all(using proof: Proof)(prem:proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      ip.cleanAssumptions
      val h1 = have(Clean.allVariables(prem))
      val h2 = have(Clean.allTypeVars(h1))
      have(withCTX(h2.statement)) by Weakening(h2)
    }
  }
  /*


  def reduceExpr[Ind](t: Expr[Ind]): Expr[Ind] = {
    t match
      case v:TypedVar   => v
      case ia: InstAbstraction => 
        val zip = ia.base.freeVars.zip(ia.insts)
        assert(zip.forall(p => p._1.typ == computeType(p._2)))
        λ(ia.base.bound, reduceExpr[Ind](ia.base.defin.body.substitute(zip.map(p => p._1 := p._2): _*)))
      case a:Abstraction => a
      case a:AppliedFunction => 
        val f = reduceExpr[Ind](a.func)
        val x = reduceExpr[Ind](a.arg)
        f*x
      case _ => t
  }



  def HOLSubst(t:Expr[Ind], x:TypedVar, u:Expr[Ind]): Expr[Ind] = {
    t match
      case v:TypedVar if v.id == x.id && v.typ == x.typ  => u
      case a:Abstraction => 
        if a.bound == x then a
        else λ(a.bound, HOLSubst(a.body, x, u))
      case a:AppliedFunction => HOLSubst(a.func, x, u)*HOLSubst(a.arg, x, u)
      case _ => t
  }

*/
}