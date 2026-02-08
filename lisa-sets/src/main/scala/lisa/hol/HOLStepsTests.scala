package lisa.hol
import lisa.hol.HOLSteps._
import lisa.utils.fol.FOL.Prop
import lisa.utils.fol.FOL.given

object HOLStepsTests extends lisa.HOL {

  private val A = typevar
  private val B = typevar
  private val C = typevar
  private val D = typevar
  private val v = typedvar(A)
  private val w = typedvar(A)
  private val x = typedvar(A)
  private val y = typedvar(A)
  private val z = typedvar(A)
  private val d = typedvar(B)
  private val e = typedvar(A ->: A)
  private val f = typedvar(A ->: B)
  private val g = typedvar(A ->: B)
  private val g2 = typedvar(A ->: B)
  private val h = typedvar(B ->: A)
  private val i = typedvar(A ->: A)
  private val p = typedvar(𝔹)
  private val q = typedvar(𝔹)
  private val r = typedvar(𝔹)
  private val b = typedvar(𝔹)

  println("pretests")

  // REFL

  val test_refl_1 = HOLTheorem(x =:= x) {
    println(x.getClass)
    have(REFL(x))
  }

  val test_refl_2 = HOLTheorem(fun(x, x) =:= fun(x, x)) {
    have(REFL(fun(x,  x)))
  }

  val test_refl_3 = HOLTheorem(fun(f,  fun(y,  f * y)) * g =:= fun(f,  fun(y,  f * y)) * g) {
    have(REFL(fun(f,  fun(y,  f * y)) * g))
  }

  // _TRANS

  println("Starting tests")
  val tt = w =:= z
  val now = System.currentTimeMillis()

  println("starting test1")

  val test_trans_1 = HOLTheorem((w =:= x, x =:= y, y =:= z) |- (w =:= z)) {
    val a1 = HOLassume(w =:= x)
    val a2 = HOLassume(x =:= y)
    val a3 = HOLassume(y =:= z)
    val s1 = have(_TRANS(a1, a2))
    have(_TRANS(s1, a3))
  }

  val test_trans_2 = HOLTheorem((x =:= z)) {
    val a1 = have(x =:= y) by Sorry
    val a2 = have(y =:= z) by Sorry
    val s1 = have(_TRANS(a1, a2))
  }

  println("starting mk_comb")
  // MK_COMB

  val test_mkcomb_1 = HOLTheorem((f =:= g, x =:= y) |- (f * x =:= g * y)) {
    val a1 = HOLassume(f =:= g)
    val a2 = HOLassume(x =:= y)
    have(MK_COMB(a1, a2))
  }

  println("starting abs")
  // ABS

  val test_abs_1 = HOLTheorem((y =:= z) |- (fun(x,  y) =:= fun(x,  z))) {
    HOLassume(y =:= z)
    have(ABS(x, A)(lastStep))
  }

  val test_abs_2 = HOLTheorem(fun(x,  fun(y,  y)) =:= fun(x,  fun(z,  z))) {
    have(fun(y,  y) =:= fun(z,  z)) by Sorry
    have(ABS(x, A)(lastStep))
  }

  val test_abs_3 = HOLTheorem(fun(x,  fun(y,  x)) =:= fun(x,  fun(z,  x))) {
    have(fun(y,  x) =:= fun(z,  x)) by Sorry
    have(ABS(x, A)(lastStep))
  }

  val test_abs_4 = HOLTheorem(fun(x,  fun(y,  f * x =:= g * (fun(z,  y) * x))) =:= fun(x,  fun(z,  z =:= x))) {
    have(fun(y,  f * x =:= g * (fun(z,  y) * x)) =:= fun(z,  z =:= x)) by Sorry
    have(ABS(x, A)(lastStep))
  }

  println("starting beta")
  // BETA
  val test_beta_1 = HOLTheorem(fun(x,  x) * x =:= x) {
    println(s"thesis: $thesis")
    have(BETA(fun(x,  x) * x))
    println(s"proof: ${lastStep.statement}")
  }

  val test_beta_2 = HOLTheorem(fun(x,  x) * x =:= (x)) {
    have(BETA(fun(x,  x) * x))
  }

  val test_beta_3 = HOLTheorem(fun(x,  y) * x =:= y) {
    have(BETA(fun(x,  y) * x))
  }

  val test_beta_4 = HOLTheorem(fun(x,  x =:= x) * x =:= (x =:= x)) {
    have(BETA(fun(x,  x =:= x) * x))
  }

  val test_beta_5 = HOLTheorem(fun(x,  x =:= y) * x =:= (x =:= y)) {
    have(BETA(fun(x,  x =:= y) * x))
  }

  val test_beta_6 = HOLTheorem(fun(x,  fun(d,  x)) * x =:= fun(d,  x)) {
    have(BETA(fun(x,  fun(d,  x)) * x))
  }

  val test_beta_7 = HOLTheorem(fun(x,  fun(d,  d)) * x =:= fun(d,  d)) {
    have(BETA(fun(x,  fun(d,  d)) * x))
  }

  val test_beta_8 = HOLTheorem(fun(x,  fun(y,  x =:= y)) * x =:= fun(y,  x =:= y)) {
    have(BETA(fun(x,  fun(y,  x =:= y)) * x))
  }

  val test_beta_9 = HOLTheorem(fun(x,  fun(d,  fun(z,  x))) * x =:= fun(d,  fun(z,  x))) {
    have(BETA(fun(x,  fun(d,  fun(z,  x))) * x))
  }

  val test_beta_10 = HOLTheorem(fun(x,  fun(y,  fun(z,  y) =:= fun(w, x))) * x =:= fun(y,  fun(z,  y) =:= fun(w, x))) {
    have(BETA(fun(x,  fun(y,  fun(z,  y) =:= fun(w, x))) * x))
  }

  println("starting eta")
  // ETA

  val test_eta_1 = HOLTheorem(fun(x,  f * x) =:= f) {
    have(ETA(x, f))
  }

  val f2 = fun(y,  y)
  val test_eta_2 = HOLTheorem(fun(x,  f2 * x) =:= f2) {
    have(ETA(x, f2))
  }

  val f3 = fun(y,  fun(z,  y))
  val test_eta_3 = HOLTheorem(fun(x,  f3 * x) =:= f3) {
    have(ETA(x, f3))
  }

  val f4 = fun(y,  fun(z,  f * y))
  val test_eta_4 = HOLTheorem(fun(x,  f4 * x) =:= f4) {
    have(ETA(x, f4))
  }

  val f5 = fun(y,  y)
  val test_eta_5 = HOLTheorem(fun(y,  f5 * y) =:= f5) {
    have(ETA(y, f5))
  }

  // ASSUME

  val test_HOLassume_1 = HOLTheorem(b |- b) {
    have(ASSUME(b))
  }

  val test_HOLassume_2 = HOLTheorem((x =:= x) |- (x =:= x)) {
    have(ASSUME(x =:= x))
  }

  val test_HOLassume_3 = HOLTheorem((fun(x,  y) =:= fun(x,  y)) |- (fun(x,  y) =:= fun(x,  y))) {
    have(ASSUME(fun(x,  y) =:= fun(x,  y)))
  }

  // test_HOLassume_4 commented out due to variable type conflicts

  val expr = fun(i, fun(x,  i * x =:= h * (f * x))) * fun(y,  i * y) * y
  val test_HOLassume_4 = HOLTheorem(expr |- expr) {
    have(ASSUME(expr))
  }

  val (a1, a2) = (p, q)
  val test_eqmp_1 = HOLTheorem(((a1 =:= a2), a1) |- a2) {
    val s1 = HOLassume(p =:= q)
    val s2 = HOLassume(p)
    have(EQ_MP(s1, s2))
  }

  val (a3, a4) = (fun(x,  p) =:= fun(x,  p), fun(p, q) * p)
  val test_eqmp_2 = HOLTheorem(((a3 =:= a4), a3) |- a4) {
    val s1 = HOLassume(a3 =:= a4)
    val s2 = HOLassume(a3)
    have(EQ_MP(s1, s2))
  }

  val test_eqmp_3 = HOLTheorem((fun(p, p) * p) |- p) {
    val s1 = have(BETA(fun(p, p) * p))
    val s2 = HOLassume(fun(p, p) * p)
    have(EQ_MP(s1, s2))
  }

  println("starting test eqmp 4")

  val test_eqmp_4 = HOLTheorem(p) {
    val s1 = have(BETA(fun(q, p) * q))
    val s2 = have(fun(q, p) * q) by Sorry
    have(EQ_MP(s1, s2))
  }

  val test_deductantisymrule_1 = HOLTheorem(((p === One) ==> (q === One), (q === One) ==> (p === One)) |- ((p =:= q) === One)) {
    assume((p === One) ==> (q === One))
    assume((q === One) ==> (p === One))
    val s1 = have(q |- p) by Restate
    val s2 = have(p |- q) by Restate
    have(DEDUCT_ANTISYM_RULE(s1, s2))
  }

  println("start inst tests")

  val test_inst_1 = HOLTheorem(q) {
    have(p) by Sorry
    have(INST(Seq((p, q)), lastStep))
  }
  val test_inst_2 = HOLTheorem(q) {
    have(q) by Sorry
    have(INST(Seq((p, p =:= p)), lastStep))
  }

  val test_inst_3 = HOLTheorem(p =:= p) {
    have(p =:= q) by Sorry
    have(INST(Seq((q, p)), lastStep))
  }

  val test_inst_4 = HOLTheorem(p =:= q) {
    have(p) by Sorry
    have(INST(Seq((p, p =:= q)), lastStep))
  }

  val test_inst_5 = HOLTheorem(fun(x,  y) * z =:= z) {
    have(fun(x,  y) * w =:= w) by Sorry
    have(INST(Seq((w, z)), lastStep))
  }

  val test_inst_6 = HOLTheorem(fun(x,  y) * z =:= y) {
    have(BETA(fun(x,  y) * x))
    have(INST(Seq((x, z)), lastStep))
  }
  val test_inst_7 = HOLTheorem(fun(x,  x) * z =:= z) {
    have(fun(x,  x) * x =:= x) by Sorry
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_8 = HOLTheorem(fun(x,  x =:= y) * z =:= (z =:= y)) {
    have(BETA(fun(x,  x =:= y) * x))
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_9 = HOLTheorem(fun(x,  fun(y,  x)) * z =:= fun(y,  z)) {
    have(BETA(fun(x,  fun(y,  x)) * x))
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_10 = HOLTheorem(fun(x,  fun(y,  y) =:= fun(y,  x)) * z =:= (fun(y,  y) =:= fun(y,  z))) {
    have(BETA(fun(x,  fun(y,  y) =:= fun(y,  x)) * x))
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_11 = HOLTheorem(fun(x,  fun(y,  fun(z,  x))) * w =:= fun(y,  fun(z,  w))) {
    have(BETA(fun(x,  fun(y,  fun(z,  x))) * x))
    have(INST(Seq((x, w)), lastStep))
  }

  val test_inst_12 = HOLTheorem(fun(p, q) * p) {
    have(fun(p, r) * p) by Sorry
    have(INST(Seq((r, q)), lastStep))
  }

  val test_inst_13 = HOLTheorem(fun(x,  fun(x,  y) * x) * y =:= y) {
    val s1 = have(BETA(fun(x,  fun(x,  y) * x) * x))
    val s2 = have(INST(Seq((x, y)), s1)) // fun(x, fun(x, y)*x)*y === fun(x, y)*y
    val s3 = have(BETA(fun(x,  y) * x)) // fun(x, y)*x =:= y
    val s4 = have(INST(Seq((x, y)), s3)) // fun(x, y)*y =:= y
    have(_TRANS(s2, s4))
  }

  val test_inst_14 = HOLTheorem(fun(x,  f * z) =:= fun(x,  f * z)) {
    val s0 = have(REFL(fun(x,  d)))
    val s1 = have(INST(Seq((d, f * z)), s0))
    val s2 = have(REFL(fun(x,  f * z)))
    have(_TRANS(s1, s2))

  }

  val test_inst_15 = HOLTheorem(fun(q, p) * p) {
    have(fun(p, r) * p) by Sorry
    have(INST(Seq((r, p)), lastStep))
  }

  val test_inst_16 = HOLTheorem(fun(x,  fun(y,  x)) * y =:= fun(z,  y)) {
    have(BETA(fun(x,  fun(y,  x)) * x))
    have(INST(Seq((x, y)), lastStep))
  }

  println("start inst_type tests")
  val test_inst_type_1 = HOLTheorem(fun(d,  d) * d =:= d) {
    have(BETA(fun(x,  x) * x))
    have(INST_TYPE(Seq((A, B)), lastStep))
    have(INST(Seq((typedvar(B, "x"), d)), lastStep))
  }

  println("start test_inst_type_2\n\n ")

  val test_inst_type_2 = HOLTheorem(fun(q, q) * p =:= p) {
    have(BETA(fun(x,  x) * x))
    have(INST_TYPE(Seq((A, 𝔹)), lastStep))
    have(INST(Seq((typedvar(𝔹, "x"), p)), lastStep))
  }

  val test_inst_type_3 = HOLTheorem(fun(f,  fun(g,  g) =:= fun(g,  f)) * g2 =:= (fun(g,  g) =:= fun(g,  g2))) {
    have(INST_TYPE(Seq((A, A ->: B)), test_inst_10))
    have(INST(Seq((typedvar(A ->: B, "z"), g2)), lastStep))
  }

}
