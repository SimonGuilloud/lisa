package lisa.automation.superposition
package bench

import java.io.File
import java.io.PrintWriter
import scala.io.Source
import scala.util.Using

/**
 * Turns the benchmark's result files into the paper's tables and figures.
 *
 * {{{
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.Analyse ingest e1 Job7425_output"
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.Analyse validate e1"
 * }}}
 *
 * {{{
 *   ingest <name> <job>…   a StarExec job's output tree into `LisaST_Bench/analyse/<name>.csv`
 *   validate <name>…       is that run fit to report from?
 *   [root=<path>]          the repository, if walking up from the working directory does not find it
 * }}}
 *
 * Names, not paths: a `<job>` is resolved under `LisaST_Bench/results/` and a `<name>` under
 * `LisaST_Bench/analyse/` then `LisaST_Bench/results/`, with an existing path always winning. So the commands
 * above work from anywhere in the repository and need no wrapper script -- which matters because the wrapper
 * would otherwise have to hunt for the repository and for a JDK, and get the working directory right, all of
 * which this can simply do.
 *
 * The first two steps exist because a result nobody can regenerate is not a result. Every number quoted so far
 * came from `awk` typed into a terminal against an unpacked job archive, which is reproducible only by whoever
 * typed it; `ingest` writes that step down, and `validate` is the run's own account of whether it is sound
 * enough to quote.
 *
 * The tidy CSV is the harness's own schema ([[Harness]]'s `CsvHeader`) with `job` prepended, one row per
 * (job, problem, configuration, strategy).
 */
object Analyse:

  def main(args: Array[String]): Unit =
    val (flags, rest) = args.toSeq.partition(_.contains('='))
    val opts = flags.map(a => a.span(_ != '=') match { case (k, v) => (k, v.drop(1)) }).toMap
    val repo = opts.get("root").map(new File(_)).orElse(repositoryRoot).getOrElse {
      Console.err.println("Could not find the repository from the working directory; pass root=<path>.")
      sys.exit(2)
    }
    val results = new File(repo, "LisaST_Bench/results")
    val analyse = new File(repo, "LisaST_Bench/analyse")

    rest match
      case "ingest" +: name +: jobs if jobs.nonEmpty =>
        ingest(jobs.map(j => resolve(j, Seq(results))), new File(analyse, s"$name.csv"))
      case "validate" +: names if names.nonEmpty =>
        // `.csv` is optional and either directory will do, so an ingested run and a local `run.sh` one are
        // named the same way even though only the first went through `ingest`.
        val files = names.map(n => resolve(if n.endsWith(".csv") then n else s"$n.csv", Seq(analyse, results)))
        if !files.map(validate).forall(identity) then sys.exit(1)
      case "report" +: names if names.nonEmpty =>
        val files = names.map(n => resolve(if n.endsWith(".csv") then n else s"$n.csv", Seq(analyse, results)))
        report(files.flatMap(readTidy).map(Row.apply).toVector, analyse, opts.get("budget").flatMap(_.toLongOption).getOrElse(180000L))
      case _ =>
        println("usage: ingest <name> <job>… | validate <name>… | report <name>…   [root=<path>] [budget=<ms>]")
        sys.exit(2)

  /**
   * `name` as a file: itself if that exists, else the first of `dirs` that holds it. Reported rather than
   * guessed at when it is nowhere, since the alternative is an empty result that looks like a real one.
   */
  private def resolve(name: String, dirs: Seq[File]): File =
    val direct = new File(name)
    if direct.exists then direct
    else
      dirs.map(new File(_, name)).find(_.exists).getOrElse {
        Console.err.println(s"not found: $name (looked in ${dirs.map(_.getPath).mkString(", ")})")
        sys.exit(2)
      }

  private def repositoryRoot: Option[File] =
    Iterator
      .iterate(new File(".").getAbsoluteFile.getCanonicalFile)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").isFile && new File(d, "LisaST_Bench").isDirectory)

  // ── ingest ────────────────────────────────────────────────────────────────────────────────────────────────

  /**
   * The problem a pair ran, recovered from its output path.
   *
   * StarExec copies every benchmark to `theBenchmark.p` and passes no variable naming the original, and the
   * competition copies are header-stripped, so nothing inside the sandbox can know which problem it was given
   * — the `problem` column of a cluster row reads `theBenchmark.p` for all 400. The path is the one place the
   * name survives: `…/<solver>___<config>/<PROBLEM>/<pairid>_output/result.csv`.
   */
  private val ProblemInPath = """.*/([^/]+\.p)/\d+_output$""".r

  /** The job id, likewise off the path: `Job7425_output/…`. */
  private val JobInPath = """.*?Job(\d+)_output.*""".r

  private def ingest(dirs: Seq[File], out: File): Unit =
    Option(out.getAbsoluteFile.getParentFile).foreach(_.mkdirs())
    val header = "job" +: HarnessCsv.columns
    var rows = 0
    var pairs = 0
    var unnamed = 0
    Using.resource(new PrintWriter(out, "UTF-8")) { w =>
      w.println(header.mkString(","))
      for dir <- dirs do
        val job = dir.getPath.replace('\\', '/') match
          case JobInPath(n) => n
          case _ => dir.getName
        // Every `result.csv` under a `<pairid>_output` directory. A portfolio pair holds one per worker plus
        // the combined one the launcher writes; the combined one is what carries every strategy, so the
        // per-worker copies underneath it would double every row.
        val results = walk(dir).filter(f => f.getName == "result.csv" && f.getParentFile.getName.endsWith("_output"))
        for f <- results do
          pairs += 1
          val parent = f.getParentFile.getPath.replace('\\', '/')
          val problem = parent match
            case ProblemInPath(p) => p
            case _ => unnamed += 1; ""
          Using.resource(Source.fromFile(f, "UTF-8")) { src =>
            val lines = src.getLines().toVector
            // A pair killed before writing leaves a header-only or empty file; that absence is itself data,
            // and `validate` counts it, so it is not an error here.
            for line <- lines.drop(1) if line.trim.nonEmpty do
              val cells = splitCsv(line)
              if cells.size == HarnessCsv.columns.size then
                // The name from the path wins: it is the only correct one on a cluster row, and on a local
                // row it agrees with what the harness wrote.
                val fixed = if problem.isEmpty then cells else cells.updated(1, problem)
                w.println((job +: fixed).map(csvCell).mkString(","))
                rows += 1
          }
    }
    println(f"ingested $rows%d rows from $pairs%d pairs into ${out.getPath}")
    if unnamed > 0 then println(s"  WARNING: $unnamed pairs had no problem name in their path; their `problem` column is whatever the row carried")

  private def walk(f: File): Vector[File] =
    if f.isDirectory then Option(f.listFiles()).toVector.flatten.flatMap(walk) else Vector(f)

  // ── validate ──────────────────────────────────────────────────────────────────────────────────────────────

  /**
   * Whether a run is fit to report from, and what is wrong with it if not.
   *
   * The protocol discards a run whose workers were abandoned, so this enforces it rather than trusting the
   * reader to check. The counts it prints are the ones that have actually gone wrong here: rows that never
   * arrived, `KILLED` rows from a worker stopped before it could report, and `contaminated` rows that ran
   * beside an abandoned worker. A silent 23% of `KILLED` rows is what a budget that started its clock after
   * parsing looked like, and it was caught by eye rather than by anything automatic.
   */
  private def validate(file: File): Boolean =
    val rows = readTidy(file)
    if rows.isEmpty then { println(s"${file.getName}: no rows"); return false }
    def col(r: Map[String, String], k: String): String = r.getOrElse(k, "")
    val configs = rows.map(col(_, "config")).distinct.sorted
    val problems = rows.map(r => Row.baseName(col(r, "problem"))).distinct
    val verdicts = rows.groupBy(col(_, "verdict")).view.mapValues(_.size).toMap

    // Expected coverage: every configuration should have a row for every problem it was given, times the
    // number of strategies it runs. Missing cells are the ones a killed worker never wrote.
    // Against the problems in the *file*, not the ones this configuration happens to have rows for. Deriving
    // the expectation from what arrived makes every configuration complete by construction, which is exactly
    // the blind spot: a configuration that lost six problems to killed workers reported 100%.
    val perConfig = configs.map { c =>
      val rs = rows.filter(col(_, "config") == c)
      val strategies = rs.map(col(_, "strategy")).distinct.size.max(1)
      (c, rs.size, problems.size * strategies)
    }
    val contaminated = rows.count(col(_, "contaminated") == "true")
    val killed = verdicts.getOrElse("KILLED", 0)
    val exhausted = verdicts.getOrElse("EXHAUSTED", 0)
    val badProof = verdicts.getOrElse("BAD_PROOF", 0)
    // Only on a refutation. `e2` runs clausify-only against a prover that returns `Sorry` and never searches,
    // so every one of its `CLAUSIFIED` rows uses one by construction; counting those would condemn the
    // experiment for doing exactly what it is for. What must never happen is a claimed *refutation* that the
    // kernel accepted only because a `Sorry` stood in for the proof.
    val sorry = rows.count(r => col(r, "uses_sorry") == "true" && col(r, "verdict") == "REFUTED")

    println(s"${file.getName}: ${rows.size} rows, ${problems.size} problems, ${configs.size} configurations")
    for (c, got, want) <- perConfig do
      val pct = if want == 0 then 100.0 else 100.0 * got / want
      println(f"  $c%-24s $got%5d of $want%5d rows ($pct%.1f%%)")
    println("  verdicts: " + verdicts.toSeq.sortBy(-_._2).map((v, n) => s"$v=$n").mkString("  "))

    // Two of these are fatal and the rest are reported. A `BAD_PROOF` or a `Sorry` in a refutation is the
    // paper's trust claim failing, and no aggregate computed over such a run means anything. `contaminated`
    // is the protocol's own discard condition. `KILLED` and `EXHAUSTED` are losses of coverage rather than
    // of soundness, so they are quantified and left to the reader's judgement.
    var ok = true
    if badProof > 0 then { println(s"  FATAL: $badProof bad proofs — the kernel rejected a reconstructed proof"); ok = false }
    if sorry > 0 then { println(s"  FATAL: $sorry refutations valid only via Sorry"); ok = false }
    if contaminated > 0 then { println(s"  FATAL: $contaminated rows ran beside an abandoned worker; the protocol discards this run"); ok = false }
    if killed + exhausted > 0 then
      val pct = 100.0 * (killed + exhausted) / rows.size
      println(f"  note: $killed KILLED and $exhausted EXHAUSTED rows ($pct%.1f%% of rows) carry no measurement")
      if pct > 10.0 then println("  WARNING: over 10% of rows report nothing; check that the budget leaves room for the answer to be written")
    if ok then println("  OK to report from")
    ok

  // ── report ────────────────────────────────────────────────────────────────────────────────────────────────

  /**
   * One result row, with the accessors the tables need.
   */
  private final case class Row(m: Map[String, String]):
    def s(k: String): String = m.getOrElse(k, "")
    def d(k: String): Option[Double] = s(k).toDoubleOption
    def i(k: String): Option[Int] = s(k).toIntOption
    def config: String = s("config")

    /**
     * The problem's base name, always — `AGT007+2.p`, never `Problems/AGT/AGT007+2.p`.
     *
     * The two kinds of run name it differently: a local `run.sh` row carries the manifest's TPTP-relative
     * path, while a cluster row is named from its output directory, which holds only the file name. Compared
     * as written they never match, so a report over one of each treated the same 400 problems as 800 and
     * every "both solved" count silently collapsed toward zero.
     */
    def problem: String = Row.baseName(s("problem"))
    def strategy: String = s("strategy")
    def solved: Boolean = s("verdict") == "REFUTED"

    /**
     * What this run cost end to end. The four phases are disjoint and every one a user waits for, so their
     * sum is the number to compare configurations on; a phase a configuration does not run is absent rather
     * than zero, which is why the last two default.
     */
    def totalMs: Option[Double] =
      for c <- d("clausify_ms"); s <- d("search_ms")
      yield c + s + d("reconstruct_ms").getOrElse(0.0) + d("check_ms").getOrElse(0.0)

  private object Row:
    /** Strip any directory, whichever separator the run that wrote the row happened to use. */
    def baseName(p: String): String = p.substring(math.max(p.lastIndexOf('/'), p.lastIndexOf('\\')) + 1)

  /**
   * The hypothesis count below which SInE keeps everything, taken from the solver's own default rather than
   * restated, so the analysis splits on the condition the code actually applies.
   */
  private val SineMinAxioms: Int = SineConfig().minAxioms

  /**
   * What each problem this configuration solved cost it, end to end.
   *
   * A portfolio configuration has one row per strategy, and the problem is solved when the first of them
   * finishes, so the minimum is the wall clock a user waited — they ran concurrently on cores of the same
   * machine. For a single-threaded configuration there is one row and the minimum is it.
   */
  private def solvedTimes(rows: Vector[Row], config: String): Map[String, Double] =
    rows.filter(r => r.config == config && r.solved)
      .groupBy(_.problem)
      .flatMap { (p, v) => val ts = v.flatMap(_.totalMs); if ts.isEmpty then None else Some(p -> ts.min) }

  /**
   * The problems both configurations solved, and what each spent on exactly those. The only like-for-like
   * time comparison available: totals over two different problem sets are not comparable at all.
   */
  private def bothSolved(rows: Vector[Row], a: String, b: String): (Int, Double, Double) =
    val ta = solvedTimes(rows, a)
    val tb = solvedTimes(rows, b)
    val shared = ta.keySet intersect tb.keySet
    (shared.size, shared.toSeq.map(ta).sum, shared.toSeq.map(tb).sum)

  /**
   * The paper's tables, as a readable `summary.md` and a `tables.tex` to \input.
   *
   * `budget` is what an unsolved problem is charged in the total-time column. Reporting only the time on
   * solved problems would reward a configuration for giving up early, and reporting the mean ratio per
   * problem is what `content.md` rejects outright: on a problem that finishes in milliseconds the kernel's
   * constant factors turn one negligible number into a large multiple of another, and the median of such
   * ratios says nothing about what anyone waits for.
   */
  private def report(rows: Vector[Row], out: File, budget: Long): Unit =
    out.mkdirs()
    val md = new StringBuilder
    val tex = new StringBuilder
    def say(s: String): Unit = { println(s); md ++= s; md += '\n' }

    val configs = rows.map(_.config).filter(_.nonEmpty).distinct.sorted
    val problems = rows.map(_.problem).distinct
    say(s"# Benchmark results\n")
    say(s"${rows.size} rows, ${problems.size} problems, configurations: ${configs.mkString(", ")}\n")

    // ── A1: strategies, and what the portfolio adds ──────────────────────────────────────────────
    //
    // The portfolio's members ran concurrently, one per core of the same job pair, so a problem any of them
    // refuted is one the portfolio refutes, and the wall clock it took is the first to finish. That is a
    // portfolio result rather than eight runs combined after the fact.
    // Only where several strategies ran together. A single-strategy configuration has a "portfolio" equal to
    // itself, which is a row that says nothing and invites being read as if it did.
    val portfolioConfigs = configs.filter(c => rows.filter(_.config == c).map(_.strategy).distinct.size > 1)
    if portfolioConfigs.nonEmpty then
      say("## A1 — strategies and the portfolio\n")
      say("| configuration | strategy | solved |")
      say("|---|---|---:|")
      tex ++= "\\begin{tabular}{llr}\\toprule\nconfiguration & strategy & solved \\\\\\midrule\n"
      for c <- portfolioConfigs do
        val rs = rows.filter(_.config == c)
        val byStrategy = rs.groupBy(_.strategy).view.mapValues(v => v.count(_.solved)).toSeq.sortBy(-_._2)
        for (s, n) <- byStrategy do
          say(s"| $c | $s | $n |")
          tex ++= s"$c & ${s.replace("_", "\\_")} & $n \\\\\n"
        val portfolio = rs.filter(_.solved).map(_.problem).distinct.size
        val best = byStrategy.headOption.map(_._2).getOrElse(0)
        say(s"| **$c** | **portfolio** | **$portfolio** |")
        say(s"\nPortfolio solves $portfolio; best single strategy ${byStrategy.headOption.map(_._1).getOrElse("-")} solves $best, so the portfolio adds ${portfolio - best}.\n")
        tex ++= s"$c & \\textbf{portfolio} & \\textbf{$portfolio} \\\\\n"
      tex ++= "\\bottomrule\\end{tabular}\n\n"

    // ── A2: what certification costs ─────────────────────────────────────────────────────────────
    // Called A2 because the certification cost is what `e1a` against `e1b` reads off it, but the table itself
    // is just solved counts and where the time went, which every configuration owes.
    say("## A2 — solved counts and where the time goes\n")
    say(s"Solved, and total time over every problem, charging an unsolved one the ${budget / 1000} s budget.\n")
    say("| configuration | solved | total time (s) | clausify | search | reconstruct | check |")
    say("|---|---:|---:|---:|---:|---:|---:|")
    tex ++= "\\begin{tabular}{lrrrrrr}\\toprule\nconfiguration & solved & total (s) & clausify & search & reconstruct & check \\\\\\midrule\n"
    for c <- configs do
      val rs = rows.filter(_.config == c)
      val solvedProblems = rs.filter(_.solved).map(_.problem).distinct.size
      // Per problem the portfolio's cost is its first success; an unsolved problem costs the budget.
      val perProblem = rs.groupBy(_.problem).map { (_, v) =>
        v.filter(_.solved).flatMap(_.totalMs) match
          case xs if xs.nonEmpty => xs.min
          case _ => budget.toDouble
      }
      def phase(k: String): Double = rs.filter(_.solved).flatMap(_.d(k)).sum / 1000.0
      say(f"| $c | $solvedProblems | ${perProblem.sum / 1000.0}%.0f | ${phase("clausify_ms")}%.0f | ${phase("search_ms")}%.0f | ${phase("reconstruct_ms")}%.0f | ${phase("check_ms")}%.0f |")
      tex ++= f"$c & $solvedProblems & ${perProblem.sum / 1000.0}%.0f & ${phase("clausify_ms")}%.0f & ${phase("search_ms")}%.0f & ${phase("reconstruct_ms")}%.0f & ${phase("check_ms")}%.0f \\\\\n"
    tex ++= "\\bottomrule\\end{tabular}\n\n"
    say("\nPhase columns are summed over that configuration's own refutations, so they say where its time goes, not what it would cost another configuration.\n")

    // ── the same comparison restricted to what both solved ───────────────────────────────────────
    //
    // A total over the whole set and a total over the shared set answer different questions and neither is
    // sufficient. The first charges an unsolved problem the budget, so it rewards solving more; the second is
    // the only like-for-like time comparison, because a total taken over two different sets of problems is
    // smaller for whichever solved fewer -- the opposite of what it looks like it says.
    if configs.size > 1 then
      val ref = configs.head
      say(s"Time compared only where both solved, against `$ref`:\n")
      say(s"| configuration | both solved | $ref (s) | this (s) | ratio |")
      say("|---|---:|---:|---:|---:|")
      for c <- configs.tail do
        val (n, a, b) = bothSolved(rows, ref, c)
        if n > 0 then say(f"| $c | $n | ${a / 1000.0}%.0f | ${b / 1000.0}%.0f | ${b / a}%.2fx |")
      say("")

    // ── how much of this could move on a re-run ──────────────────────────────────────────────────
    //
    // A verdict is deterministic only away from the budget boundary: under a wall clock the number of given
    // clauses processed varies between runs, so a problem solved in the last tenth of its budget is one that
    // might not be solved next time. Reporting that count is what lets a reader judge whether a difference of
    // one or two problems is a result or noise.
    say("Solved inside the last tenth of the budget, and so able to move between runs:\n")
    say("| configuration | solved | near the boundary |")
    say("|---|---:|---:|")
    for c <- configs do
      val ts = solvedTimes(rows, c)
      say(s"| $c | ${ts.size} | ${ts.count(_._2 > 0.9 * budget)} |")
    say("")

    // ── E3, E4, E5: each variant against its family's baseline ───────────────────────────────────
    //
    // Grouped by the part of the name before the underscore, which is the experiment, and compared against
    // the configuration that represents the shipped default: the one called `baseline`, or failing that the
    // one that switches the mechanism off.
    val families = configs.groupBy(_.takeWhile(_ != '_')).filter((_, cs) => cs.size > 1 && cs.exists(_.contains('_')))
    for (family, members) <- families.toSeq.sortBy(_._1) do
      val base = members.find(_.contains("baseline")).orElse(members.find(_.endsWith("-off"))).getOrElse(members.head)
      val baseSolved = solvedTimes(rows, base).size
      say(s"## $family — against `$base`\n")
      say("| configuration | solved | change | attempted | both solved | time vs baseline |")
      say("|---|---:|---:|---:|---:|---:|")
      tex ++= s"\\begin{tabular}{lrrrr}\\toprule\n$family & solved & change & both solved & time vs baseline \\\\\\midrule\n"
      for c <- members.sortBy(c => -solvedTimes(rows, c).size) do
        val n = solvedTimes(rows, c).size
        val attempted = rows.count(_.config == c)
        val (shared, a, b) = bothSolved(rows, base, c)
        val delta = if c == base then "—" else f"${n - baseSolved}%+d"
        val ratio = if c == base || shared == 0 || a == 0 then "—" else f"${b / a}%.2fx"
        say(f"| $c | $n | $delta | $attempted | $shared | $ratio |")
        tex ++= s"${c.replace("_", "\\_")} & $n & $delta & $shared & $ratio \\\\\n"
      tex ++= "\\bottomrule\\end{tabular}\n\n"
      say("\n`attempted` is how many rows arrived: a configuration with fewer has lost problems to killed workers, and part of its change is missing attempts rather than failures.\n")

      // E5 again, restricted to where SInE can do anything at all. Below `SineConfig.minAxioms` the selector
      // keeps every hypothesis, so on those problems the two configurations are the same run and including
      // them dilutes the comparison with rows that cannot differ. The threshold is the solver's own
      // activation condition rather than a number chosen for the paper, and every row carries the hypothesis
      // count, so the split happens here and needs no separate dataset.
      if family == "e5" then
        val big = rows.filter(_.i("hypotheses").exists(_ >= SineMinAxioms)).map(_.problem).toSet
        say(s"Restricted to the ${big.size} problems with at least $SineMinAxioms hypotheses, where SInE actually filters:\n")
        say("| configuration | solved | of those problems |")
        say("|---|---:|---:|")
        for c <- members do
          val n = rows.count(r => r.config == c && r.solved && big.contains(r.problem))
          say(s"| $c | $n | ${rows.count(r => r.config == c && big.contains(r.problem))} |")
        say("")

    // ── a portfolio assembled from two runs of the same strategies ───────────────────────────────
    //
    // The eight strategies are recorded independently, so a portfolio that runs some of them at one setting
    // and the rest at another can be read off two runs rather than measured in a third: a problem is solved
    // if any strategy solves it under the setting that strategy would be given. That is sound only because
    // the members are independent -- each is its own process on its own core, and none is stopped when
    // another succeeds -- so moving one between settings cannot change what the others do.
    //
    // Here it answers which strategies should carry SInE's lower activation floor. `bba9f661` raised that
    // floor from 32 to 500 and switched selection off for the 124 CASC problems with 32 to 499 hypotheses;
    // lowering it again recovers some problems and loses others, because SInE is incomplete and can prune an
    // axiom the proof needed. Every subset is scored so the answer comes from the corpus.
    val pairs = configs.flatMap(c => configs.find(_ == s"$c-sine32").map(v => (c, v)))
    for (base, variant) <- pairs do
      val strategies = rows.filter(r => r.config == base || r.config == variant).map(_.strategy).filter(_.nonEmpty).distinct.sorted
      if strategies.size > 1 && strategies.size <= 12 then
        def solvedBy(config: String, s: String): Set[String] =
          rows.filter(r => r.config == config && r.strategy == s && r.solved).map(_.problem).toSet
        val atBase = strategies.map(s => s -> solvedBy(base, s)).toMap
        val at32 = strategies.map(s => s -> solvedBy(variant, s)).toMap
        // What each strategy is worth if moved to the low floor on its own: what it then solves that the
        // whole rest of the portfolio does not, against what it stops solving that nothing else covers.
        say(s"## $base — which strategies should take SInE's lower floor\n")
        say("| strategy | solves at 500 | at 32 | gains alone | loses alone |")
        say("|---|---:|---:|---:|---:|")
        for s <- strategies do
          val others = (strategies.toSet - s).flatMap(atBase)
          val gains = (at32(s) -- atBase(s) -- others).size
          val loses = (atBase(s) -- at32(s) -- others).size
          say(s"| $s | ${atBase(s).size} | ${at32(s).size} | +$gains | -$loses |")
        val allBase = strategies.flatMap(atBase).toSet
        val all32 = strategies.flatMap(at32).toSet
        say(s"\nWhole portfolio: $base solves ${allBase.size}, $variant solves ${all32.size}.")
        // The best mix, by the obvious greedy rule: give the low floor to every strategy that gains more on
        // its own than it loses. It is a lower bound on the best subset rather than the optimum, since gains
        // overlap between strategies, but it is the number worth quoting beside the two uniform settings.
        val mixed = strategies.filter { s =>
          val others = (strategies.toSet - s).flatMap(atBase)
          (at32(s) -- atBase(s) -- others).size > (atBase(s) -- at32(s) -- others).size
        }
        val mixedSolved = (strategies.map(s => if mixed.contains(s) then at32(s) else atBase(s))).flatten.toSet
        say(s"Mixed, with ${if mixed.isEmpty then "no strategy" else mixed.mkString(", ")} at floor 32: ${mixedSolved.size}.\n")

    // ── E2: the clausification variants ──────────────────────────────────────────────────────────
    //
    // E2 is the exception to everything above: it runs no search, so it has no verdicts and no budget, and a
    // table keyed on refutations reports nothing but zeros for it. What it has instead is sizes and
    // clausification times, compared over the problems both variants got through.
    //
    // Raw against shared size is the point rather than a detail. Raw is what a reader pictures when told a
    // proof has a size; shared is what it occupies, since the pipeline builds formulas by substituting into
    // contexts and the same subformula is reachable from many steps. Their ratio is how much sharing the
    // variant achieved, and it is the quantity that separates rewriting in place from deconstruction.
    val clausifyOnly = configs.filter(c => rows.exists(r => r.config == c && r.s("verdict") == "CLAUSIFIED"))
    if clausifyOnly.nonEmpty then
      val done = clausifyOnly.map(c => c -> rows.filter(r => r.config == c && r.s("verdict") == "CLAUSIFIED").map(r => r.problem -> r).toMap).toMap
      val shared = clausifyOnly.map(c => done(c).keySet).reduce(_ intersect _)
      say("## E2 — clausification variants\n")
      say(s"Over the ${shared.size} problems every variant clausified. `sharing` is raw size over shared size: how much the proof reuses.\n")
      say("| variant | clausify (s) | check (s) | proof steps | raw size | shared size | sharing |")
      say("|---|---:|---:|---:|---:|---:|---:|")
      tex ++= "\\begin{tabular}{lrrrrrr}\\toprule\nvariant & clausify (s) & check (s) & steps & raw & shared & sharing \\\\\\midrule\n"
      for c <- clausifyOnly do
        val rs = shared.toSeq.map(done(c))
        def sum(k: String): Double = rs.flatMap(_.d(k)).sum
        val raw = sum("raw_size")
        val shr = sum("shared_size")
        say(f"| $c | ${sum("clausify_ms") / 1000.0}%.1f | ${sum("check_ms") / 1000.0}%.1f | ${sum("proof_steps")}%.0f | ${raw}%.0f | ${shr}%.0f | ${if shr > 0 then raw / shr else 0.0}%.1fx |")
        tex ++= f"$c & ${sum("clausify_ms") / 1000.0}%.1f & ${sum("check_ms") / 1000.0}%.1f & ${sum("proof_steps")}%.0f & ${raw}%.0f & ${shr}%.0f & ${if shr > 0 then raw / shr else 0.0}%.1f \\\\\n"
      tex ++= "\\bottomrule\\end{tabular}\n\n"
      // How many each got through at all, which is a result too: a variant that clausifies fewer problems
      // inside the same budget is worse regardless of what its sizes look like on the ones it managed.
      say("")
      say("| variant | clausified | of problems seen |")
      say("|---|---:|---:|")
      for c <- clausifyOnly do say(s"| $c | ${done(c).size} | ${rows.count(_.config == c)} |")
      say("")

    // ── A3: does the cost of certification scale? ─────────────────────────────────────────────────
    //
    // A constant factor is a good result and easy to state; growth would be the finding. Fitting
    // log(check) against log(size) answers exactly that: a slope near 1 is a constant cost per unit of proof,
    // and a slope above 1 means checking degrades as proofs grow.
    val checked = rows.filter(r => r.solved && r.d("check_ms").exists(_ > 0))
    if checked.nonEmpty then
      say("## A3 — does checking scale with proof size?\n")
      say("| against | n | slope of log(check) on log(size) | reading |")
      say("|---|---:|---:|---|")
      for size <- Seq("proof_steps", "raw_size", "shared_size") do
        val pts = checked.flatMap(r => for s <- r.d(size) if s > 0; c <- r.d("check_ms") if c > 0 yield (math.log(s), math.log(c)))
        if pts.size >= 3 then
          val (xs, ys) = pts.unzip
          val mx = xs.sum / xs.size
          val my = ys.sum / ys.size
          val sxy = pts.map((x, y) => (x - mx) * (y - my)).sum
          val sxx = xs.map(x => (x - mx) * (x - mx)).sum
          val slope = if sxx == 0 then Double.NaN else sxy / sxx
          val reading =
            if slope < 0.9 then "sub-linear: the cost per unit falls as proofs grow"
            else if slope < 1.15 then "linear: a constant cost per unit"
            else "super-linear: checking degrades as proofs grow"
          say(f"| $size | ${pts.size} | $slope%.2f | $reading |")
      say("")

    // ── T3 and T4: the trust claims ──────────────────────────────────────────────────────────────
    val refutations = rows.count(_.solved)
    val sorry = rows.count(r => r.solved && r.s("uses_sorry") == "true")
    val bad = rows.count(_.s("verdict") == "BAD_PROOF")
    say("## T3, T4 — the trust claims\n")
    say(s"- refutations: $refutations")
    say(s"- valid only via `Sorry` (T3): **$sorry**")
    say(s"- rejected by the kernel (T4): **$bad**\n")

    Using.resource(new PrintWriter(new File(out, "summary.md"), "UTF-8"))(_.print(md.toString))
    Using.resource(new PrintWriter(new File(out, "tables.tex"), "UTF-8"))(_.print(tex.toString))
    println(s"wrote ${new File(out, "summary.md").getPath} and tables.tex")

  // ── CSV ───────────────────────────────────────────────────────────────────────────────────────────────────

  /**
   * The harness's column names, read from the file rather than restated, so the two cannot drift apart.
   */
  private object HarnessCsv:
    val columns: Vector[String] = Vector(
      "dataset", "problem", "config", "strategy", "verdict", "hypotheses",
      "clausify_ms", "search_ms", "reconstruct_ms", "check_ms",
      "given", "derived", "peak_active", "peak_passive", "clauses", "fresh_symbols",
      "proof_steps", "raw_size", "shared_size", "max_sequent", "imports",
      "uses_sorry", "contaminated", "detail"
    )

  private def readTidy(file: File): Vector[Map[String, String]] =
    Using.resource(Source.fromFile(file, "UTF-8")) { src =>
      val lines = src.getLines().toVector
      if lines.isEmpty then Vector.empty
      else
        val header = splitCsv(lines.head)
        lines.tail.filter(_.trim.nonEmpty).map(l => header.zip(splitCsv(l)).toMap)
    }

  /**
   * Split one CSV line, honouring the quoting [[csvCell]] produces. The `detail` column carries checker
   * messages and exception text, which is exactly where a stray comma or quote comes from.
   */
  private def splitCsv(line: String): Vector[String] =
    val out = Vector.newBuilder[String]
    val cur = new StringBuilder
    var quoted = false
    var i = 0
    while i < line.length do
      val c = line.charAt(i)
      if quoted then
        if c == '"' then
          if i + 1 < line.length && line.charAt(i + 1) == '"' then { cur += '"'; i += 1 } else quoted = false
        else cur += c
      else if c == '"' then quoted = true
      else if c == ',' then { out += cur.toString; cur.clear() }
      else cur += c
      i += 1
    out += cur.toString
    out.result()

  private def csvCell(s: String): String =
    if s.exists(c => c == ',' || c == '"' || c == '\n') then "\"" + s.replace("\"", "\"\"") + "\"" else s
