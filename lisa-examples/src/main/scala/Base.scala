import lisa.maths.SetTheory.Base.Pair.{*, given}
import lisa.maths.SetTheory.Functions.Function.{*, given}

object Base extends lisa.Main:

  private val R = variable[Ind]
  private val f = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]

  // define simple infix notations for relations and binary functions

  val infixRelation = DEF(λ(R, λ(x, λ(y, pair(x)(y) ∈ R)))).printAs(args =>
      val r = args(0)
      val x = args(1)
      val y = args(2)
      s"$x ${r} $y"
    )

  object IRel:
    def apply(R: Expr[Ind], x: Expr[Ind], y: Expr[Ind]): Expr[Prop] = infixRelation(R)(x)(y)

    def unapply(e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind], Expr[Ind])] = e match
      case App(App(App(`infixRelation`, r), x), y) => Some((r, x, y))
      case _ => None


  val infixBinaryFunction = DEF(λ(f, λ(x, λ(y, app(f)(pair(x)(y)))))).printAs(args =>
      val f = args(0)
      val x = args(1)
      val y = args(2)
      s"($x ${f} $y)"
    )

  object IBinFun:
    def apply(f: Expr[Ind], x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = infixBinaryFunction(f)(x)(y)

    def unapply(e: Expr[Ind]): Option[(Expr[Ind], Expr[Ind], Expr[Ind])] = e match
      case App(App(App(`infixBinaryFunction`, f), x), y) => Some((f, x, y))
      case _ => None

  functionBetween.printAs(args =>
      val f = args(0)
      val x = args(1)
      val y = args(2)
      s"$f :: $x → $y"
  )

  extension (f: Expr[Ind]) {

    /**
     * Notation `f :: A -> B`
     */
    infix def ::(fType: (Expr[Ind], Expr[Ind])): Expr[Prop] =
      val (a, b) = fType
      functionBetween(f)(a)(b)
  }

  def replace2[A, B](e: Expr[A], l: Expr[B], r: Expr[B]): Expr[A] =
    if e == l then r.asInstanceOf[Expr[A]]
    else e match
      case App(f, arg) => App(replace2(f, l, r), replace2(arg, l, r))
      case Abs(v, body) =>
        val frees = l.freeVars ++ r.freeVars
        if frees.contains(v) then
          val v1 = v.freshRename(frees)
          Abs(v1, replace2(body.substituteUnsafe(Map(v -> v1)), l, r)).asInstanceOf[Expr[A]]
        else
          Abs(v, replace2(body, l, r))
      case _ => e

  extension [A] (e: Expr[A])
    infix def replace(l: Expr[A], r: Expr[A]): Expr[A] = replace2(e, l, r)

  extension (s: Sequent)
    def toFormula = 
        if s.left.isEmpty then 
            if s.right.isEmpty then ⊤ else s.right.reduce(and(_)(_))
        else if s.right.isEmpty then
            s.left.reduce(or(_)(_)) ==> bot
        else
            s.left.reduce(or(_)(_)) ==> s.right.reduce(or(_)(_))


  def findBestAtom(f: Expr[Prop]): Expr[Prop] = Tautology.findBestAtom(f.underlying).map(asFrontExpression).get.asInstanceOf[Expr[Prop]]

end Base