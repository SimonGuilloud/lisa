package lisa.automation.superposition
package bench

import java.io.File
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import scala.io.Codec
import scala.io.Source
import scala.jdk.StreamConverters._
import scala.util.Using

/**
 * Builds the benchmark manifests. Run once; the outputs are committed, so reproducing the paper does not
 * require running this — reproducing the *draw* does.
 *
 * {{{
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets"
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets seed=7 size=50"
 * }}}
 *
 * It does three things: draws TPTP400 from the library, checks the CASC manifest still resolves, and mirrors
 * both into the classpath resources that [[ProblemList]] reads.
 *
 * @param seed the draw's seed (default 42)
 * @param size how many problems to draw (default 400)
 * @param root the repository, if it cannot be found by walking up from the working directory
 */
object BuildDatasets:

  /** A problem and the header fields the draw and the analysis need. */
  private case class Entry(path: String, spc: String):
    def form: String = spc.takeWhile(_ != '_') //          FOF or CNF
    def status: String = spc.split("_").lift(1).getOrElse("") // THM, UNS, CAX
    def domain: String = path.split("/").lift(1).getOrElse("")

  /** Refutable and first order: all this prover can attempt at all. */
  private val eligibleSpc = "^(FOF_(THM|UNS|CAX)|CNF_UNS)_".r

  def main(args: Array[String]): Unit =
    val opts = args.flatMap(a => a.split("=", 2) match { case Array(k, v) => Some(k -> v); case _ => None }).toMap
    val seed = opts.get("seed").map(_.toLong).getOrElse(42L)
    val size = opts.get("size").map(_.toInt).getOrElse(400)

    val tptp = BenchUtil.tptpRootOrExplain().getOrElse(sys.exit(2))
    val repo = opts.get("root").map(new File(_)).orElse(repositoryRoot).getOrElse {
      println("Could not find the repository from the working directory; pass root=<path>.")
      sys.exit(2)
    }
    val datasets = new File(repo, "LisaST_Bench/datasets")
    val resources = new File(repo, "lisa-sets/src/main/resources/lisa/automation/superposition")

    // ── the pool ────────────────────────────────────────────────────────────────────────────────
    val scanned = scan(tptp)
    println(s"scanned ${scanned.size} problems with an SPC header")
    val pool = scanned.filter(e => eligibleSpc.findPrefixOf(e.spc).isDefined)
    println(s"pool: ${describe(pool)} refutable first-order problems")

    // Disjoint from the CASC half, so the two tables are independent samples rather than overlapping ones.
    val cascFile = new File(datasets, "casc-j13-fof.txt")
    val casc = readLines(cascFile).toSet
    val eligible = pool.filterNot(e => casc(e.path))
    println(s"eligible: ${describe(eligible)} after excluding the ${casc.size} CASC problems")

    // ── the draw ────────────────────────────────────────────────────────────────────────────────
    //
    // Sorted first, so the draw does not depend on the order the file system handed the library over, and
    // then shuffled exactly as [[ProblemList.sample]] shuffles — one notion of "seeded draw" in the project.
    val ordered = eligible.sortBy(_.path)
    val drawn = new scala.util.Random(seed).shuffle(ordered).take(size).sortBy(_.path)
    val manifest = new File(datasets, s"tptp$size.txt")
    write(manifest, drawn.map(_.path))
    // A sidecar rather than extra columns in the manifest: `ProblemList` reads one path per line, while the
    // analysis wants to split results by form (FOF against CNF) and by domain without needing $TPTP.
    write(
      new File(datasets, s"tptp$size.csv"),
      "problem,form,status,spc,domain" +: drawn.map(e => s"${e.path},${e.form},${e.status},${e.spc},${e.domain}")
    )
    println(s"wrote $manifest (${describe(drawn)}, seed $seed)")

    // ── verify the CASC manifest ────────────────────────────────────────────────────────────────
    //
    // It cannot be rebuilt from the library, being the competition's own problem list, so it is checked
    // instead: every path must resolve, or a run silently measures fewer problems than it reports.
    val missing = casc.toSeq.sorted.filterNot(p => new File(tptp, p).isFile)
    missing.foreach(p => println(s"  missing: $p"))
    if missing.nonEmpty then
      println(s"${missing.size} CASC problems are not in this TPTP installation")
      sys.exit(1)
    println(s"verified $cascFile: all ${casc.size} problems present")

    // ── mirror to the classpath ─────────────────────────────────────────────────────────────────
    //
    // `ProblemList` loads a manifest as a resource, so a forked child or a jar finds it whatever the working
    // directory is. The copies under `datasets/` are the ones a reader of the artefact looks at.
    for f <- Seq(cascFile, manifest) do Files.copy(f.toPath, new File(resources, f.getName).toPath, java.nio.file.StandardCopyOption.REPLACE_EXISTING)
    println(s"mirrored to $resources")

  /**
   * Every problem in the library with the Specialist Problem Class from its header: `FOF_THM_RFO_SEQ` is a
   * first-order formula problem whose status is Theorem, with equality. Problems without the header — there
   * are none in a well-formed installation — are dropped.
   *
   * The header sits within the first hundred lines or so, after the `Syntax` block, so reading stops there
   * rather than at the end of a file that may be hundreds of megabytes. Latin-1, because the decoder must not
   * throw on a stray byte in a comment.
   */
  private def scan(tptp: File): Vector[Entry] =
    val root = tptp.toPath.resolve("Problems")
    val files = Using(Files.walk(root, 2))(_.toScala(Vector).filter(p => Files.isRegularFile(p) && p.toString.endsWith(".p"))).get
    files.flatMap { p =>
      val spc = Using(Source.fromFile(p.toFile)(using Codec.ISO8859)) { src =>
        src.getLines().take(120).collectFirst { case l if l.startsWith("% SPC") => l.dropWhile(_ != ':').drop(1).trim }
      }.toOption.flatten
      spc.map(s => Entry(relative(root.getParent, p), s))
    }

  /** A library-relative path, always with `/`: the manifests are read on every platform. */
  private def relative(base: Path, p: Path): String = base.relativize(p).toString.replace('\\', '/')

  /** `n (f FOF, c CNF)`, the shape of a set of problems in one phrase. */
  private def describe(es: Seq[Entry]): String =
    val fof = es.count(_.form == "FOF")
    s"${es.size} ($fof FOF, ${es.size - fof} CNF)"

  /** The repository: the nearest enclosing directory holding both `build.sbt` and the artefact. */
  private def repositoryRoot: Option[File] =
    Iterator
      .iterate(new File(".").getAbsoluteFile.getCanonicalFile)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").isFile && new File(d, "LisaST_Bench").isDirectory)

  private def readLines(f: File): Vector[String] =
    Using(Source.fromFile(f))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get

  private def write(f: File, lines: Seq[String]): Unit =
    Using(new PrintWriter(f, "UTF-8"))(w => lines.foreach(w.println)).get
