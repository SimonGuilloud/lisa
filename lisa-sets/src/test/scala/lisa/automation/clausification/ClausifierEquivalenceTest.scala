package lisa.automation.clausification

import lisa.automation.superposition.TptpCorpus
import lisa.automation.superposition.bench.EqFofEvaluation
import lisa.automation.superposition.bench.FofEvaluation
import lisa.automation.superposition.bench.ProblemList
import lisa.tptp.AnnotatedFormula
import lisa.tptp.AnnotatedSequent
import lisa.tptp.KernelParser.axiomLikeRoles
import lisa.tptp.KernelParser.problemToKernel
import lisa.tptp.KernelParser.strictMapAtom
import lisa.tptp.KernelParser.strictMapTerm
import lisa.tptp.KernelParser.strictMapVariable
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

import java.io.File
import scala.util.Failure
import scala.util.Success
import scala.util.Try

import Clausification.GeneratedNames

/**
 * Equivalence check between the **uncertified** clausifier ([[lisa.automation.clausification.UncertifiedClausifier]])
 * and the **certified** one ([[CertifiedClausifier]]), on real TPTP input. It establishes two things per input
 * formula: that the two make the *same naming decisions*, the certified named formula being equal to the
 * uncertified one *identically* since both mint their `nm` atoms with the same generator
 * ([[CertifiedClausifier.sameNaming]] is a plain `==`); and that they Skolemize to the same formula up to
 * renaming of the fresh symbols. This is the soundness lever: if the certified (kernel-checked) path names and
 * Skolemizes the same way, its clauses vouch for the uncertified path's.
 *
 * By default it runs a 20 + 20 seeded sample of the equality-free and equality-bearing FOF lists, which keeps
 * `sbt test` short. [[Corpus]] says how the environment scales it up to a whole benchmark corpus without a
 * rebuild, which is how the artefact backs the claim at the size the paper reports it.
 *
 * Needs the `TPTP` env var (the directory containing `Problems/`); skipped otherwise.
 */
class ClausifierEquivalenceTest extends AnyFunSuite:

  private def size(e: K.Expression): Int = e match
    case K.Application(f, a) => 1 + size(f) + size(a)
    case K.Lambda(_, b) => 1 + size(b)
    case _ => 1

  /**
   * Run `body` on a daemon thread, returning `Some(result)` if it finishes within `ms`, else interrupting it and
   *  returning `None`. Used to skip formulas whose certified ε-Skolemization blows up (until it shares terms).
   */
  private def runWithTimeout[A](ms: Long)(body: => A): Option[A] =
    val result = new java.util.concurrent.atomic.AtomicReference[Option[A]](None)
    val th = new Thread(() =>
      try result.set(Some(body))
      catch case _: Throwable => ()
    )
    th.setDaemon(true)
    th.start()
    th.join(ms)
    if th.isAlive then { th.interrupt(); None }
    else result.get

  /**
   * Structural equality up to renaming of the **fresh** symbols, with the problem symbols (all other constants)
   *  matching exactly. Two classes of fresh symbol, treated differently:
   *
   *   - **Ordinary variables** (clause variables `w…` or originals, and naming atoms `nm…`) must match by a
   *     consistent **bijection** (distinct on one side ⇒ distinct on the other).
   *   - **Skolem symbols**, `sk…` (uncertified, a Skolem `Constant`) and `feps…` (certified, the ε-abstraction function),
   *     match by a consistent **forward function** only (uncertified ⇒ certified), NOT a bijection. Uncertified mints a fresh
   *     Skolem per existential; on the side compared here identical ε-terms abstract to the same `feps` symbol, so
   *     syntactically-identical existentials *merge* (the certified clausifier itself does not: it mints a fresh `esk`
   *     per occurrence). So uncertified is a strict refinement: every uncertified Skolem maps onto one certified symbol, but one
   *     certified symbol may cover several uncertified ones. Requiring only the forward map captures exactly this (and more
   *     distinct Skolem functions is unconditionally sound, so the relaxation loses no soundness assurance).
   */
  // Returns None if isomorphic (in the above sense), else the first structurally-mismatching subexpression pair.
  private def isoMismatch(x: K.Expression, y: K.Expression): Option[(K.Expression, K.Expression)] =
    val fwd = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression]
    val bwd = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression]
    // Skolem symbols: uncertified's `sk` (a Constant), the certified path's `esk` (a schematic Variable), and the
    // test's `feps` ε-abstraction. Matched by name regardless of Constant/Variable so ε↔Skolem-function
    // representations line up. (Counter is in the identifier's `no` field, so the `name` is exactly the prefix.)
    def isSkolem(e: K.Expression): Boolean =
      val name = e match { case c: K.Constant => c.id.name; case v: K.Variable => v.id.name; case _ => "" }
      name == GeneratedNames.uncertifiedSkolem || name == "feps" || name == GeneratedNames.skolemFun
    def renamable(e: K.Expression): Boolean = e.isInstanceOf[K.Variable] || isSkolem(e)
    def go(a: K.Expression, b: K.Expression): Option[(K.Expression, K.Expression)] = (a, b) match
      case (K.Application(f1, a1), K.Application(f2, a2)) => go(f1, f2).orElse(go(a1, a2))
      case (K.Lambda(_, _), _) | (_, K.Lambda(_, _)) => if a == b then None else Some((a, b))
      case _ if isSkolem(a) && isSkolem(b) => if fwd.getOrElseUpdate(a, b) == b then None else Some((a, b)) // forward only
      case _ if renamable(a) && renamable(b) => if fwd.getOrElseUpdate(a, b) == b && bwd.getOrElseUpdate(b, a) == a then None else Some((a, b))
      case _ => if a == b then None else Some((a, b))
    go(x, y)

  private def isoUpToRenaming(x: K.Expression, y: K.Expression): Boolean = isoMismatch(x, y).isEmpty

  /**
   * ε-abstraction for the test: replace each `ε(λx.φ)` by a fresh function `F` applied to the ε-term's **Ind**
   *  free variables (sorted by original name), matching UncertifiedClausifier's Skolem functions. Unlike `Clausal.Abstraction`
   *  this filters to `Ind` (the certified path names before Skolem, so ε-terms can contain predicate naming atoms,
   *  which are not Skolem-function arguments). Run *before* ∀-strip so `F`'s arguments carry the original names.
   *
   *  ε-terms are treated as **fully opaque** uninterpreted function symbols: we never look inside one (so nested
   *  ε-terms are absorbed into their enclosing symbol, exactly as UncertifiedClausifier's opaque Skolem functions absorb
   *  the witnesses they range over), and its identity is the *raw* ε-term, of which only the free variables are observable.
   *  Keying on the raw term (rather than recursively pre-abstracting the body) makes dedup structural: two identical
   *  ε-terms get one symbol regardless of the numbering order of any inner ε-terms.
   */
  private def absEps(e: K.Expression): K.Expression =
    var n = 0
    val memo = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression] // same raw ε-term ⇒ same symbol
    def go(e: K.Expression): K.Expression = e match
      case eps @ K.Application(f0, _) if f0 == K.epsilon => // an ε-term is opaque, so do NOT descend into its body
        memo.getOrElseUpdate(
          eps, {
            // A **Constant** (like UncertifiedClausifier's Skolem `sk`), NOT a Variable: else a nullary `feps` (result sort
            // Ind) would be an Ind-valued free variable and cascade in as an argument to outer Skolem functions.
            val fv = eps.freeVariables.toSeq.filter(_.sort == K.Ind).sortBy(v => (v.id.name, v.id.no))
            val fSym = K.Constant(K.Identifier("feps", n), fv.foldRight(K.Ind: K.Sort)((v, acc) => v.sort -> acc))
            n += 1
            fv.foldLeft(fSym: K.Expression)((acc, v) => K.Application(acc, v))
          }
        )
      case K.Application(f, a) => K.Application(go(f), go(a))
      case K.Lambda(x, b) => K.Lambda(x, go(b))
      case _ => e
    go(e)

  /**
   * Which problems the check runs on, and where its counts go. Read from the environment so that the same
   * test serves both `sbt test` and the corpus run the artefact reports:
   *
   *   - `CLAUSIFIER_EQUIV_LIST`     a manifest of TPTP-root-relative paths: either a file, or the name of a
   *                                 packaged list such as `casc-j13-fof.txt`. Unset means the default pair.
   *   - `CLAUSIFIER_EQUIV_N`        how many problems to draw from it, or `all` (default 20 per list)
   *   - `CLAUSIFIER_EQUIV_SEED`     the draw's seed (default 42)
   *   - `CLAUSIFIER_EQUIV_FORMULAS` at most this many formulas per problem, drawn with the same seed (default: all)
   *   - `CLAUSIFIER_EQUIV_BUDGET_S` stop after this many seconds (default: run to the end of the list)
   *   - `CLAUSIFIER_EQUIV_OUT`      append the run's counts to this CSV
   *
   * The per-problem cap is what puts a large corpus in reach, and it trades depth for breadth deliberately. A
   * CASC problem carries some 40000 formulas, nearly all of them axioms from files shared across a whole
   * domain, so checking one exhaustively costs hours and then re-checks those same axioms on the next problem.
   * Capping spends the time on the 400 distinct conjectures instead.
   *
   * Stopping on the budget is not a failure either. The check is a conjunction over formulas, so any subset of
   * them is a weaker claim of the same kind; the CSV row records how many formulas were checked out of how
   * many were seen, which is what the paper has to quote rather than "the corpus".
   */
  private object Corpus:
    private def env(key: String): Option[String] = sys.env.get(key).map(_.trim).filter(_.nonEmpty)

    private val listName: Option[String] = env("CLAUSIFIER_EQUIV_LIST")
    private val n: Int = env("CLAUSIFIER_EQUIV_N").fold(20)(s => if s.equalsIgnoreCase("all") then Int.MaxValue else s.toInt)
    private val seed: Long = env("CLAUSIFIER_EQUIV_SEED").fold(42L)(_.toLong)
    private val out: Option[File] = env("CLAUSIFIER_EQUIV_OUT").map(new File(_))

    val budgetMs: Option[Long] = env("CLAUSIFIER_EQUIV_BUDGET_S").map(_.toLong * 1000)

    /** What was run on, for the report. */
    val name: String = listName.getOrElse("fof-noeq+fof-eq")

    /** The formulas of one problem to check: all of them, or a seeded draw when a cap is set. */
    def formulasOf(all: Seq[K.Expression]): Seq[K.Expression] =
      env("CLAUSIFIER_EQUIV_FORMULAS").map(_.toInt) match
        case Some(cap) if cap < all.size => new scala.util.Random(seed).shuffle(all).take(cap)
        case _ => all

    val problems: Vector[String] = listName match
      case None => FofEvaluation.sample(n, seed) ++ EqFofEvaluation.sample(n, seed)
      case Some(list) =>
        // `ProblemList` treats the env var's own value as the override file, so one setting names either a
        // path on disk or, when it is not a file, a packaged list -- no "is this a path?" test to get wrong.
        val available = new ProblemList(list, Some("CLAUSIFIER_EQUIV_LIST"))
        if n >= available.all.size then available.all else available.sample(n, seed)

    /** Append `row` to the CSV, writing `header` first if the file is new. Does nothing when unconfigured. */
    def record(header: String, row: String): Unit = out.foreach { f =>
      val fresh = !f.exists() || f.length() == 0
      val w = new java.io.PrintWriter(new java.io.FileWriter(f, true))
      try
        if fresh then w.println(header)
        w.println(row)
      finally w.close()
    }

  /**
   * Hypothesis formulas + the negated conjecture, exactly as the clausifier pipeline sees them.
   */
  private def inputFormulas(parsed: lisa.tptp.TptpProblem): Seq[K.Expression] =
    val hyps = parsed.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => f.formula
    }
    val negConj = parsed.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.neg(f.formula)
    }
    hyps ++ negConj.toSeq

  // ── clause-set equivalence ──────────────────────────────────────────────────────────────────────
  //
  // The check above compares the two paths formula by formula, which stops short of the clauses: it says
  // nothing about distribution or about how the matrix is finally split. What the prover actually receives is
  // the clause set, and E1 compares the two paths on searches driven by it, so that is what has to agree.

  /**
   * The Skolem symbol behind `e`, if it is one. The two paths represent them differently — the certified path
   * as a schematic [[K.Variable]] named `esk`, the uncertified as a [[K.Constant]] named `sk` — so this is the
   * one place where the clause sets legitimately differ and the only thing the comparison maps.
   */
  private def skolemId(e: K.Expression): Option[K.Identifier] = e match
    case c: K.Constant if c.id.name == GeneratedNames.uncertifiedSkolem => Some(c.id)
    case v: K.Variable if v.id.name == GeneratedNames.skolemFun => Some(v.id)
    case _ => None

  /** One literal as a string, with Skolem symbols and ordinary variables named by the given functions. */
  private def renderLiteral(e: K.Expression, sk: K.Identifier => String, vr: K.Identifier => String): String =
    def go(e: K.Expression): String = skolemId(e) match
      case Some(id) => sk(id)
      case None =>
        e match
          case v: K.Variable => vr(v.id)
          case c: K.Constant => c.id.toString
          case K.Application(f, a) => s"${go(f)}(${go(a)})"
          case K.Lambda(x, b) => s"λ${vr(x.id)}.${go(b)}"
    go(e)

  /**
   * One clause as a canonical string, given a naming for Skolem symbols.
   *
   * A sequent's sides are `Set`s, so literal order carries no information and cannot be compared directly.
   * Literals are therefore ordered by their *anonymised* rendering, and only then are variables numbered by
   * first occurrence in that order — two passes, because numbering variables first would make the numbering
   * depend on the set's iteration order, which is exactly what is not trustworthy.
   */
  private def canonicalClause(s: K.Sequent, sk: K.Identifier => String): String =
    // Clause variables are numbered per clause, by first occurrence. Their absolute numbers are not part of
    // the clause: a clause is implicitly universally quantified, so `w_196` and `w_88` name the same variable
    // of the same clause, and the two paths reach a given clause having minted different numbers of variables
    // before it. What must agree is which positions share a variable, which is what the numbering captures.
    //
    // Two passes, because a sequent's sides are `Set`s and literal order carries no information: literals are
    // ordered by their rendering with variables anonymous (Skolems are already globally numbered by the
    // caller, which is what makes this order discriminating), and only then are variables numbered.
    val key = (e: K.Expression) => renderLiteral(e, sk, _ => "V")
    val left = s.left.toSeq.sortBy(key)
    val right = s.right.toSeq.sortBy(key)
    val nums = scala.collection.mutable.LinkedHashMap.empty[K.Identifier, Int]
    def number(e: K.Expression): Unit =
      if skolemId(e).isEmpty then
        e match
          case v: K.Variable => nums.getOrElseUpdate(v.id, nums.size)
          case K.Application(f, a) => number(f); number(a)
          case K.Lambda(x, b) => nums.getOrElseUpdate(x.id, nums.size); number(b)
          case _ => ()
    (left ++ right).foreach(number)
    val vr = (id: K.Identifier) => s"V${nums.getOrElse(id, -1)}"
    // Sorted *after* numbering, not left in the numbering order. Literals that render alike while anonymous —
    // three `ssList(V)` in one clause, say — tie in the pass above, and the tie is broken by `Set` iteration
    // order, differently on each side. The numbering is unaffected (it is driven by the untied literals), so
    // the two sides produce the same multiset of rendered literals in a different order, and sorting settles it.
    s"${left.map(renderLiteral(_, sk, vr)).sorted.mkString(",")} |- ${right.map(renderLiteral(_, sk, vr)).sorted.mkString(",")}"

  /**
   * A clause set as a canonical list of strings: clauses ordered by their Skolem-agnostic form, then Skolem
   * symbols numbered by first occurrence in that order. Two sets that agree up to a bijection on Skolem
   * symbols render identically; a set that mints a *different number* of them does not, so the certified
   * path's fresh-per-occurrence Skolems would show as a mismatch rather than be quietly accepted.
   */
  private def canonicalClauses(cs: Seq[K.Sequent]): Seq[String] =
    val ordered = cs.sortBy(canonicalClause(_, _ => "SK"))
    val nums = scala.collection.mutable.LinkedHashMap.empty[K.Identifier, Int]
    // Number by walking the ordered clauses, so the numbering depends only on the canonical order.
    ordered.foreach(s => (s.left.toSeq ++ s.right.toSeq).sortBy(renderLiteral(_, _ => "SK", _.toString)).foreach { e =>
      def walk(x: K.Expression): Unit = skolemId(x) match
        case Some(id) => nums.getOrElseUpdate(id, nums.size)
        case None =>
          x match
            case K.Application(f, a) => walk(f); walk(a)
            case K.Lambda(_, b) => walk(b)
            case _ => ()
      walk(e)
    })
    ordered.map(canonicalClause(_, id => s"SK${nums.getOrElse(id, -1)}"))

  /** The clause set the certified pipeline hands its prover, captured with a `Sorry` back end. */
  private def certifiedClauses(p: lisa.automation.Problem): Seq[K.Sequent] =
    var captured: lisa.automation.Problem = null
    CertifiedClausifier.certifyClausal(p, q => { captured = q; K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), q.imports) })
    captured.imports.toSeq

  test("certified and uncertified clausifier name AND Skolemize equivalently across the corpus") {
    val root = TptpCorpus.rootOrCancel("the uncertified/certified naming equivalence check")
    val problems = Corpus.problems
    val startedAt = System.currentTimeMillis()
    val deadline = Corpus.budgetMs.map(startedAt + _)
    var found = 0 // selected problems whose file is actually under `root`
    var problemsChecked = 0 // ... of those, the ones that parsed
    var formulasSeen = 0 // formulas the parsed problems contain, before the per-problem cap
    var formulasChecked = 0
    var oversize = 0 // formulas skipped as too big to check in reasonable time
    var skolemTimeouts = 0 // formulas whose certified ε-Skolemization did not finish in 2s
    var overBudget = 0 // ... or ran the clausifier out of heap, which is the same fact caught by a different guard
    val skolemFails = scala.collection.mutable.ListBuffer.empty[(String, Option[(K.Expression, K.Expression)])]
    // Both of these are asserted empty at the end, but collected rather than thrown: a run over a whole corpus
    // that dies on its first bad formula reports nothing at all -- not the count, not the other problems, not
    // even how far it got -- which is exactly the information needed to act on the failure.
    val namingFails = scala.collection.mutable.ListBuffer.empty[String]
    val errors = scala.collection.mutable.ListBuffer.empty[(String, Throwable)]
    val unparsed = scala.collection.mutable.ListBuffer.empty[(String, Throwable)]

    val pending = problems.iterator
    while pending.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
      val rel = pending.next()
      val f = new File(root, rel)
      if f.exists then
        found += 1
        // Catch Throwable, not just NonFatal: the TPTP parser can StackOverflow on very large problems.
        val parsedOpt: Option[lisa.tptp.TptpProblem] =
          try Some(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
          catch
            case t: Throwable =>
              unparsed += ((rel, t)) // named, not just counted: "396 of 400 parsed" invites asking which four
              None
        parsedOpt.foreach { parsed =>
          problemsChecked += 1
          val available = inputFormulas(parsed)
          formulasSeen += available.size
          // The deadline is polled per formula, not only per problem: one CASC problem is some 40000 formulas
          // and hours of work, so a between-problems poll lets a single problem overrun the budget many times
          // over -- which it did, before this.
          val toCheck = Corpus.formulasOf(available).iterator
          while toCheck.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
            val phi = toCheck.next()
            if size(phi) > 8000 then oversize += 1 // `findSite` is superlinear, so a giant formula stalls the run
            else
              val t0 = System.nanoTime()
              // Catch Throwable: over a corpus the clausifier meets formulas that overflow the stack, and one
              // of those must not take the other 399 problems' results with it.
              try
                // (1) after naming: the certified and uncertified named formulas agree *identically* (same `nm` generator).
                if !CertifiedClausifier.sameNaming(phi) then namingFails += rel
                // (2) after Skolem: uncertified (Skolem functions) equals certified (ε-terms, ∀-stripped, ε-abstracted).
                // Some LCL modal problems build exponentially-large ε-terms (until the certified Skolemization shares
                // them properly), so run the certified side under a 2s budget and count a timeout as unchecked.
                val uncertifiedSk = CertifiedClausifier.uncertifiedNamedNnfSkolem(phi) // linear (Skolem functions), always cheap
                runWithTimeout(2000) { CertifiedClausifier.stripForall(absEps(CertifiedClausifier.namedNnfSkolemEps(phi))) } match
                  case None => skolemTimeouts += 1; println(f"[timer] TIMEOUT  size=${size(phi)}%6d  $rel")
                  case Some(certSk) =>
                    if !isoUpToRenaming(uncertifiedSk, certSk) then skolemFails += ((rel, isoMismatch(uncertifiedSk, certSk)))
                    formulasChecked += 1
              catch
                // The clausifier's own valve (`Clausification.checkInterrupted`, a heap ceiling) reports the
                // same fact as the 2s cap: this formula's ε-Skolemization blew up. So it is a skip, like a
                // timeout, and only counted. Anything else is a bug and has to fail the run.
                case t @ (_: InterruptedException | _: OutOfMemoryError) =>
                  overBudget += 1
                  println(f"[timer] RESOURCE size=${size(phi)}%6d  $rel: ${t.getMessage}")
                case t: Throwable =>
                  errors += ((rel, t))
                  println(f"[timer] ERROR    size=${size(phi)}%6d  $rel: $t")
              // `println` (not `info`): sbt buffers `info` to test-end, so it is useless for watching progress live.
              val ms = (System.nanoTime() - t0) / 1000000
              if ms > 1000 then println(f"[timer] ${ms}%6d ms  size=${size(phi)}%6d  $rel")
        }

    val stoppedEarly = deadline.exists(System.currentTimeMillis() >= _)
    val elapsedS = (System.currentTimeMillis() - startedAt) / 1000
    val divergentProblems = (namingFails ++ skolemFails.map(_._1)).distinct.size
    val summary =
      s"${Corpus.name}: $problemsChecked of $found problems parsed, out of ${problems.size} selected; " +
        s"$formulasChecked of $formulasSeen formulas checked ($oversize oversize, $skolemTimeouts over 2s, $overBudget over heap, ${errors.size} errored); " +
        s"${namingFails.size} naming and ${skolemFails.size} skolem divergences in $divergentProblems problems; ${elapsedS}s" +
        (if stoppedEarly then " (stopped on budget)" else "")
    println(s"[summary] $summary")
    unparsed.foreach((p, t) => println(s"[summary]   unparsed: $p: $t"))
    namingFails.distinct.foreach(p => println(s"[summary]   naming-diverge: $p"))
    skolemFails.foreach((p, m) => println(s"[summary]   skolem-diverge: $p: $m"))
    errors.map((p, t) => s"$p: $t").distinct.foreach(e => println(s"[summary]   error: $e"))
    info(summary)
    Corpus.record(
      "list,selected,found,parsed,formulas_seen,formulas,oversize,timeouts,over_heap,errors," +
        "naming_divergences,skolem_divergences,divergent_problems,elapsed_s,stopped_early",
      Seq(Corpus.name, problems.size, found, problemsChecked, formulasSeen, formulasChecked, oversize, skolemTimeouts, overBudget, errors.size,
        namingFails.size, skolemFails.size, divergentProblems, elapsedS, stoppedEarly).mkString(",")
    )

    assert(found > 0, s"none of the ${problems.size} selected problems exist under $root; is the corpus complete?")
    // Without this a parser regression would show up only as a quietly smaller check, the divergence assertions
    // below still passing over whatever survived.
    assert(problemsChecked * 4 >= found * 3, s"only $problemsChecked of $found problems parsed")
    assert(formulasChecked > 0)
    assert(namingFails.isEmpty, s"${namingFails.size} naming divergences (e.g. ${namingFails.headOption})")
    assert(skolemFails.isEmpty, s"${skolemFails.size} skolem divergences (e.g. ${skolemFails.headOption})")
    assert(errors.isEmpty, s"${errors.size} formulas raised (e.g. ${errors.headOption.map((p, t) => s"$p: $t")})")
  }

  /**
   * T1: the two clausifiers are the same transformation, compared where it matters — on the clause sets the
   * prover receives, per problem, up to a bijection on Skolem symbols.
   *
   * This is the precondition E1 rests on. The two paths are compared on searches, and a search is driven by
   * its clause set: if the sets differed, a difference in solved counts would say nothing about the cost of
   * certification. The formula-level check above is upstream of distribution and of the final clause split,
   * so it cannot establish this.
   *
   * Filtered by clausification '''time''', not by problem size, so that the shapes excluded are the ones that
   * are genuinely slow rather than the ones that merely look large — a size filter drops exactly the blow-up
   * cases this is meant to cover. What was skipped is counted and reported.
   */
  test("certified and uncertified clausifiers produce the same clause set for each problem") {
    val root = TptpCorpus.rootOrCancel("the uncertified/certified clause-set check")
    val problems = Corpus.problems
    val startedAt = System.currentTimeMillis()
    val deadline = Corpus.budgetMs.map(startedAt + _)
    var checked = 0
    var slow = 0 // clausification did not finish in the per-problem budget
    var renamedOnly = 0 // same clause count, strings differ only by fresh-symbol naming
    val mismatches = scala.collection.mutable.ListBuffer.empty[(String, Int, Int)]
    val errors = scala.collection.mutable.ListBuffer.empty[(String, Throwable)]

    val pending = problems.iterator
    while pending.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
      val rel = pending.next()
      val f = new File(root, rel)
      if f.exists then
        val parsed =
          try Some(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
          catch case _: Throwable => None
        parsed.foreach { p =>
          val hyps = p.formulas.collect { case a: AnnotatedFormula if axiomLikeRoles.contains(a.role) => K.Sequent(Set.empty, Set(a.formula)) }
          val conj = p.formulas.collectFirst { case a: AnnotatedFormula if a.role == "conjecture" => K.Sequent(Set.empty, Set(a.formula)) }
          val problem = lisa.automation.Problem(hyps, conj)
          // Both sides under one budget, since either can be the slow one and the comparison needs both.
          runWithTimeout(20000) {
            (canonicalClauses(certifiedClauses(problem)), canonicalClauses(UncertifiedClausifier.clausalForm(problem).hypotheses))
          } match
            case None => slow += 1; println(s"[clauses] SLOW $rel")
            case Some((cert, uncert)) =>
              checked += 1
              // Counts are asserted; exact equality is only reported, for now. The two paths still name their
              // fresh symbols differently -- the uncertified keeps the input's variable names (`U`, `A`) where
              // the certified mints its own (`w_196`), and their `nm` counters advance independently
              // (`nm_5` against `nm_87`) -- so the strings differ where the clauses do not. Counts are the
              // part that is a property of the clause set rather than of a naming convention, and they became
              // equal once `DistributePhase.clausesOf` absorbed `⊤`/`⊥` as the uncertified path does.
              if cert.size != uncert.size then
                mismatches += ((rel, cert.size, uncert.size))
                println(s"[clauses] COUNT DIFFERS $rel  certified=${cert.size} uncertified=${uncert.size}")
                cert.diff(uncert).take(2).foreach(c => println(s"[clauses]   only certified:   $c"))
                uncert.diff(cert).take(2).foreach(c => println(s"[clauses]   only uncertified: $c"))
              else if cert != uncert then
                renamedOnly += 1
                if renamedOnly <= 2 then
                  println(s"[clauses] naming differs (same ${cert.size} clauses): $rel")
                  cert.diff(uncert).take(1).foreach(c => println(s"[clauses]   certified:   $c"))
                  uncert.diff(cert).take(1).foreach(c => println(s"[clauses]   uncertified: $c"))
        }

    val summary =
      s"${Corpus.name}: clause sets agree on ${checked - mismatches.size} of $checked problems " +
        s"($slow too slow, ${errors.size} errored) in ${(System.currentTimeMillis() - startedAt) / 1000}s"
    println(s"[clauses] $summary")
    info(summary)
    assert(checked > 0, "no problem was checked")
    assert(mismatches.isEmpty, s"${mismatches.size} problems produce a different NUMBER of clauses, e.g. ${mismatches.headOption}")
  }
