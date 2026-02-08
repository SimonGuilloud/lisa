package lisa.hol
import lisa.hol.HOLSteps._
import lisa.utils.fol.FOL.{_, given}

/**
 * Example HOL theorems in Lisa, demonstrating multi-step proofs
 * combining primitive deduction rules.
 */
object HOLExample extends lisa.HOL {

  private val A = typevar
  private val B = typevar
  private val C = typevar

  private val x = typedvar(A)
  private val y = typedvar(A)
  private val z = typedvar(A)
  private val w = typedvar(A)

  private val d = typedvar(B)
  private val e = typedvar(C)

  private val f = typedvar(A ->: B)
  private val g = typedvar(A ->: B)

  private val p = typedvar(𝔹)
  private val q = typedvar(𝔹)
  private val r = typedvar(𝔹)


  // 1. Beta-normalisation chains

  /** ⊢ (λx. (λx. y)(x))(y) = y */
  val DOUBLE_BETA = HOLTheorem(fun(x, fun(x, y) * x) * y =:= y) {
    val s1 = have(BETA(fun(x, fun(x, y) * x) * x))
    val s2 = have(INST(Seq((x, y)), s1))
    val s3 = have(BETA(fun(x, y) * x))
    val s4 = have(INST(Seq((x, y)), s3))
    have(_TRANS(s2, s4))
  }

  /** ⊢ (λx. (λy. y)(x))(z) = z */
  val COMPOSE_ID = HOLTheorem(fun(x, fun(y, y) * x) * z =:= z) {
    val s1 = have(BETA(fun(x, fun(y, y) * x) * x))
    val s2 = have(INST(Seq((x, z)), s1))
    val s3 = have(BETA(fun(y, y) * y))
    val s4 = have(INST(Seq((y, z)), s3))
    have(_TRANS(s2, s4))
  }

  /** ⊢ (λx. (λy. (λx. y))(x))(w) = (λx. w) */
  val MULTI_BETA = HOLTheorem(fun(x, fun(y, fun(x, y)) * x) * w =:= fun(x, w)) {
    val b1 = have(BETA(fun(x, fun(y, fun(x, y)) * x) * x))
    val b1w = have(INST(Seq((x, w)), b1))
    val b2 = have(BETA(fun(y, fun(x, y)) * y))
    val b2w = have(INST(Seq((y, w)), b2))
    have(_TRANS(b1w, b2w))
  }


  // 2. ABS + BETA: simplifying under a binder

  /** ⊢ (λx. (λy. y)(x)) = (λx. x) */
  val BETA_UNDER_LAMBDA = HOLTheorem(fun(x, fun(y, y) * x) =:= fun(x, x)) {
    val b = have(BETA(fun(y, y) * x))
    have(ABS(x, A)(b))
  }

  /** ⊢ (λx. (λy. z)(x)) = (λx. z) */
  val CONST_UNDER_LAMBDA = HOLTheorem(fun(x, fun(y, z) * x) =:= fun(x, z)) {
    val b = have(BETA(fun(y, z) * x))
    have(ABS(x, A)(b))
  }

  /** ⊢ (λx. λd. (λd. d)(d)) = (λx. λd. d) */
  val DOUBLE_ABS = HOLTheorem(fun(x, fun(d, fun(d, d) * d)) =:= fun(x, fun(d, d))) {
    val b = have(BETA(fun(d, d) * d))
    val abs1 = have(ABS(d, B)(b))
    have(ABS(x, A)(abs1))
  }


  // 3. MK_COMB + ABS: congruence under binders

  /** f = g ⊢ (λx. f(x)) = (λx. g(x)) */
  val CONG_ABS = HOLTheorem((f =:= g) |- (fun(x, f * x) =:= fun(x, g * x))) {
    val h = HOLassume(f =:= g)
    val comb = have(MK_COMB(h, have(REFL(x))))
    have(ABS(x, A)(comb))
  }

  /** ⊢ (λx. (λx. f(x))(x)) = f — double eta-expansion round-trip. */
  val DOUBLE_ETA = HOLTheorem(fun(x, fun(x, f * x) * x) =:= f) {
    val beta = have(BETA(fun(x, f * x) * x))
    val abs = have(ABS(x, A)(beta))
    val eta = have(ETA(x, f))
    have(_TRANS(abs, eta))
  }


  // 4. Propositional reasoning via DEDUCT_ANTISYM_RULE + EQ_MP

  /** (λp. q)(r) ⊢ q — modus ponens through beta. */
  val BETA_MP = HOLTheorem((fun(p, q) * r) |- q) {
    val beta = have(BETA(fun(p, q) * r))
    val h = HOLassume(fun(p, q) * r)
    have(EQ_MP(beta, h))
  }

  /** ⊢ (λp. p)(p) = p */
  val BOOL_BETA_EQ = HOLTheorem(fun(p, p) * p =:= p) {
    have(BETA(fun(p, p) * p))
  }

  /** ⊢ p = p — via DEDUCT_ANTISYM_RULE. */
  val BOOL_REFL_VIA_DEDUCT = HOLTheorem(p =:= p) {
    val h1 = have(ASSUME(p))
    have(DEDUCT_ANTISYM_RULE(h1, h1))
  }

  /** q ⊢ q */
  val DEDUCT_AND_MP = HOLTheorem(q |- q) {
    val fwd = have(EQ_MP(have(BETA(fun(p, q) * r)), HOLassume(fun(p, q) * r)))
    have(ASSUME(q))
  }

}

