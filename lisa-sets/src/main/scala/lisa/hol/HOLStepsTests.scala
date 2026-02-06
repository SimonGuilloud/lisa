
package lisa.hol
import lisa.hol.HOLSteps.*
import lisa.utils.prooflib.BasicStepTactic.* 
import lisa.utils.fol.FOL as F
import F.{Expr, Ind, Prop, >>:, variable, given}

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
  private val h = typedvar(B ->: A)
  private val i = typedvar(A ->: A)
  private val p = typedvar(𝔹)
  private val q = typedvar(𝔹)
  private val r = typedvar(𝔹)
  private val b = typedvar(𝔹)

  println("pretests")


  // REFL

  val test_refl_1 = HOLTheorem(x =:= x) {
    have(REFL(x))
  }

  val test_refl_2 = HOLTheorem(fun(x::A, x) =:= fun(x::A, x)) {
    have(REFL(fun(x::A, x)))
  }

  val test_refl_3 = HOLTheorem(fun(f:: A ->: B, fun(y::A, f*y))*g =:= fun(f:: A ->: B, fun(y::A, f*y))*g) {
    have(REFL(fun(f:: A ->: B, fun(y::A, f*y))*g))
  }

  // _TRANS

  println("Starting tests")
  val tt = w =:=z
  val now = System.currentTimeMillis()

  println("starting test1")

  val test_trans_1 = HOLTheorem((w =:= x, x =:= y, y =:= z) |- (w =:=z)) {
    val a1 = HOLassume(w =:= x)
    val a2 = HOLassume(x =:= y)
    val a3 = HOLassume(y =:= z)
    val s1 = have(_TRANS(a1, a2))
    have(_TRANS(s1, a3))
  }

    val test_trans_2 = HOLTheorem((x =:=z)) {
    val a1 = have(x =:= y) by Sorry
    val a2 = have(y =:= z) by Sorry
    val s1 = have(_TRANS(a1, a2))
  }

  
  println("starting mk_comb")
  // MK_COMB

  val test_mkcomb_1 = HOLTheorem((f =:= g, x =:= y) |- (f*x =:= g*y)) {
    val a1 = HOLassume(f =:= g)
    val a2 = HOLassume(x =:= y)
    have(MK_COMB(a1, a2))
  }


  println("starting abs")
  // ABS

  val test_abs_1 = HOLTheorem((y =:= z) |- (fun(x::A, y) =:= fun(x::A, z))) {
    HOLassume(y =:= z)
    have(ABS(x, A)(lastStep))
  }


  
  val test_abs_2 = HOLTheorem(fun(x::A, fun(y::A, y)) =:= fun(x::A, fun(z::A, z))) {
    have(fun(y::A, y) =:= fun(z::A, z)) by Sorry
    have(ABS(x, A)(lastStep))
  }
  
  

  val test_abs_3 = HOLTheorem(fun(x::A, fun(y::A, x)) =:= fun(x::A, fun(z::A, x))) {
    have(fun(y::A, x) =:= fun(z::A, x)) by Sorry
    have(ABS(x, A)(lastStep))
  }

  val test_abs_4 = HOLTheorem(fun(x::A, fun(y::A, f*x =:= g*(fun(z::A, y)*x))) =:= fun(x::A, fun(z::A, z =:= x))) {
    have(fun(y::A, f*x =:= g*(fun(z::A, y)*x)) =:= fun(z::A, z =:= x)) by Sorry
    have(ABS(x, A)(lastStep))
  }
  

  println("starting beta")
  // BETA
  val test_beta_1 = HOLTheorem( fun(x::A, x)*x =:= x) {
    // Don't HOLassume x::A since we're abstracting over x
    println(s"thesis: $thesis")
    have(BETA(fun(x::A, x)*x))
    println(s"proof: ${lastStep.statement}")
  }

  val test_beta_2 = HOLTheorem(fun(x::A, x)*x =:= (x)) {
    // Don't HOLassume x::A since we're abstracting over x
    have(BETA(fun(x::A, x)*x))
  }

  val test_beta_3 = HOLTheorem(fun(x::A, y)*x =:= y) {
    have(BETA(fun(x::A, y)*x))
  }

  val test_beta_4 = HOLTheorem(fun(x::A, x =:= x)*x =:= (x =:= x)) {
    have(BETA(fun(x::A, x =:= x)*x))
  }

  val test_beta_5 = HOLTheorem(fun(x::A, x =:= y)*x =:= (x =:= y)) {
    have(BETA(fun(x::A, x =:= y)*x))
  }

  val test_beta_6 = HOLTheorem(fun(x::A, fun(y::B, x))*x =:= fun(y::B, x)) {
    have(BETA(fun(x::A, fun(y::B, x))*x))
  }

  val test_beta_7 = HOLTheorem(fun(x::A, fun(y::B, y))*x =:= fun(y::B, y)) {
    have(BETA(fun(x::A, fun(y::B, y))*x))
  }

  val test_beta_8 = HOLTheorem(fun(x::A, fun(y::A, x =:= y))*x =:= fun(y::A, x =:= y)) {
    have(BETA(fun(x::A, fun(y::A, x =:= y))*x))
  }


  val test_beta_9 = HOLTheorem(fun(x::A, fun(y::B, fun(z::A, x)))*x =:= fun(y::B, fun(z::A, x))) {
    have(BETA(fun(x::A, fun(y::B, fun(z::A, x)))*x))
  }

  val test_beta_10 = HOLTheorem(fun(x::A, fun(y::A, fun(z::A, y) =:= fun(w::A, x)))*x =:= fun(y::A, fun(z::A, y) =:= fun(w::A, x))) {
    have(BETA(fun(x::A, fun(y::A, fun(z::A, y) =:= fun(w::A, x)))*x))
  }



  println("starting eta")
  // ETA

  val test_eta_1 = HOLTheorem(fun(x::A, f*x) =:= f) {
    have(ETA(x, f))
  }

  val f2 = fun(y::A, y)
  val test_eta_2 = HOLTheorem(fun(x::A, f2*x) =:= f2) {
    have(ETA(x, f2))
  }


  val f3 = fun(y::A, fun(z::A, y))
  val test_eta_3 = HOLTheorem(fun(x::A, f3*x) =:= f3) {
    have(ETA(x, f3))
  }

  val f4 = fun(y::A, fun(z::A, f*y))
  val test_eta_4 = HOLTheorem(fun(x::A, f4*x) =:= f4) {
    have(ETA(x, f4))
  }


  val f5 = fun(y::A, y)
  val test_eta_5 = HOLTheorem(fun(y::A, f5*y) =:= f5) {
    have(ETA(y, f5))
  }





  // ASSUME

  val test_HOLassume_1 = HOLTheorem(b |- b) {
    have(ASSUME(b))
  }

  val test_HOLassume_2 = HOLTheorem((x =:= x) |- (x =:= x)) {
    have(ASSUME(x =:= x))
  }

  val test_HOLassume_3 = HOLTheorem((fun(x::A, y) =:= fun(x::A, y)) |- (fun(x::A, y) =:= fun(x::A, y)) ){
    have(ASSUME(fun(x::A, y) =:= fun(x::A, y)))
  }

  // test_HOLassume_4 commented out due to variable type conflicts

  val expr = fun(i::(A ->: A), fun(x::A, i*x =:= h*(f*x)))*fun(y::A, i*y)*y
  val test_HOLassume_4 = HOLTheorem(expr |- expr ){
    have(ASSUME(expr))
  }
  

  val (a1, a2) = (p, q)
  val test_eqmp_1 = HOLTheorem(((a1 =:= a2), a1) |- a2) {
    val s1 = HOLassume(p =:= q)
    val s2 = HOLassume(p)
    have(EQ_MP(s1, s2))
  }

  
  val (a3, a4) = (fun(x::A, p) =:= fun(x::A, p), fun(p::𝔹, q)*p)
  val test_eqmp_2 = HOLTheorem(((a3 =:= a4), a3) |- a4) {
    val s1 = HOLassume(a3 =:= a4)
    val s2 = HOLassume(a3)
    have(EQ_MP(s1, s2))
  }
  

  val test_eqmp_3 = HOLTheorem((fun(p::𝔹, p)*p) |- p ) {
    val s1 = have(BETA(fun(p::𝔹, p)*p))
    val s2 = HOLassume(fun(p::𝔹, p)*p)
    have(EQ_MP(s1, s2))
  }
  
  println("starting test eqmp 4")

  val test_eqmp_4 = HOLTheorem(p) {
    val s1 = have(BETA(fun(q::𝔹, p)*q))
    val s2 = have(fun(q::𝔹, p)*q) by Sorry
    have(EQ_MP(s1, s2))
  }


  val test_deductantisymrule_1 = HOLTheorem(((p === One) ==> (q === One), (q === One) ==> (p === One)) |- ((p =:= q) === One)){
    assume((p === One) ==> (q === One))
    assume((q === One) ==> (p === One))
    val s1 = have(q |- p) by Restate
    val s2 = have(p |- q) by Restate
    have(DEDUCT_ANTISYM_RULE(s1, s2))
  }
  
  
  println("start inst tests")

  val test_inst_1 = HOLTheorem(q){
    have(p) by Sorry
    have(INST(Seq((p, q)), lastStep))
  }
  val test_inst_2 = HOLTheorem(q) {
    have(q) by Sorry
    have(INST(Seq((p, p=:=p)), lastStep))
  }

  val test_inst_3 = HOLTheorem(p =:= p){
    have(p =:= q) by Sorry
    have(INST(Seq((q, p)), lastStep))
  }
  
  val test_inst_4 = HOLTheorem(p =:= q) {
    have(p) by Sorry
    have(INST(Seq((p, p=:=q)), lastStep))
  }

  val test_inst_5 = HOLTheorem(fun(x::A, y)*z =:= z){
    have(fun(x::A, y)*w =:= w) by Sorry
    have(INST(Seq((w, z)), lastStep))
  }

  val test_inst_6 = HOLTheorem(fun(x::A, y)*z =:= y){
    have(BETA(fun(x::A, y)*x))
    have(INST(Seq((x, z)), lastStep))
  }
  val test_inst_7 = HOLTheorem(fun(x::A, x)*z =:= z){
    have(fun(x::A, x)*x =:= x) by Sorry
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_8 = HOLTheorem(fun(x::A, x =:= y)*z =:= (z =:= y)){
    have(BETA(fun(x::A, x =:= y)*x))
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_9 = HOLTheorem(fun(x::A, fun(y::A, x))*z =:= fun(y::A, z)){
    have(BETA(fun(x::A, fun(y::A, x))*x))
    have(INST(Seq((x, z)), lastStep))
  }


  val test_inst_10 = HOLTheorem(fun(x::A, fun(y::A, y) =:= fun(y::A, x))*z =:= (fun(y::A, y) =:= fun(y::A, z))){
    have(BETA(fun(x::A, fun(y::A, y) =:= fun(y::A, x))*x))
    have(INST(Seq((x, z)), lastStep))
  }

  val test_inst_11 = HOLTheorem(fun(x::A, fun(y::A, fun(z::A, x)))*w =:= fun(y::A, fun(z::A, w))){
    have(BETA(fun(x::A, fun(y::A, fun(z::A, x)))*x))
    have(INST(Seq((x, w)), lastStep))
  }

  val test_inst_12 = HOLTheorem(fun(p::𝔹, q)*p){
    have(fun(p::𝔹, r)*p) by Sorry
    have(INST(Seq((r, q)), lastStep))
  }

  val test_inst_13 = HOLTheorem(fun(x::A, fun(x::A, y)*x)*y =:= y){
    val s1 = have(BETA(fun(x::A, fun(x::A, y)*x)*x))
    val s2 = have(INST(Seq((x, y)), s1)) // fun(x, fun(x, y)*x)*y === fun(x, y)*y
    val s3 = have(BETA(fun(x::A, y)*x)) // fun(x, y)*x =:= y
    val s4 = have(INST(Seq((x, y)), s3)) // fun(x, y)*y =:= y
    have(_TRANS(s2, s4))
  }


  val test_inst_14 = HOLTheorem(fun(x::A, f*z) =:= fun(x::A, f*z)){
    val s0 = have(REFL(fun(x::A, d)))
    val s1 = have(INST(Seq((d, f*z)), s0))
    val s2 = have(REFL(fun(x::A, f*z) ))
    have(_TRANS(s1, s2))

  }


  // Those don't hold because they require alpha equivalence to conclude the proof.

  println("Starting test 15")
  val test_inst_15 = HOLTheorem(fun(q::𝔹, p)*p){
    have(fun(p::𝔹, r)*p) by Sorry
    have(INST(Seq((r, p)), lastStep))
  }

  println("Starting test 16")
  val test_inst_16 = HOLTheorem(fun(x::A, fun(y::A, x))*y =:= fun(z::A, y)){
    have(BETA(fun(x::A, fun(y::A, x))*x))
    have(INST(Seq((x, y)), lastStep))
  }


}