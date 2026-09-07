package lisa.automation.superposition
package bench

import scala.collection.mutable

import lisa.utils.K.Application
import lisa.utils.K.Expression
import lisa.utils.K.Lambda
import lisa.utils.K.SCProof
import lisa.utils.K.SCProofStep
import lisa.utils.K.SCSubproof
import lisa.utils.K.Sequent

/**
 * Size of a reconstructed kernel proof, in the four quantities the benchmarks report.
 *
 * @param steps      proof steps, a subproof counting as its body plus one ([[SCProof.totalLength]])
 * @param rawSize    node count over every formula of every step conclusion, with no sharing
 * @param sharedSize the same count with each distinct subexpression counted once
 * @param maxSequent the largest single step conclusion, by node count
 * @param imports    number of imports, which are not included in any of the sizes above
 */
final case class ProofMetrics(steps: Int, rawSize: Long, sharedSize: Long, maxSequent: Long, imports: Int)

/**
 * '''Why two sizes.''' The kernel hash-conses expressions, so a subformula reachable from many steps is one
 * object. `rawSize` is the proof as a reader imagines it, every occurrence counted; `sharedSize` is what it
 * occupies, each distinct subexpression counted once. The pipeline builds formulas by substituting into
 * contexts, so the two diverge widely and the gap is itself reported.
 *
 * Sharing is detected by [[Expression.uniqueNumber]], which is per object and therefore shared exactly when
 * hash-consing made two structurally equal expressions the same object. That is the default; it is disabled by
 * setting `lisa.hashcons` or `LISA_HASHCONS` to `false`, and with it off `sharedSize` degenerates to `rawSize`.
 *
 * Imports are excluded from the sizes, matching `totalLength`, and reported as a count instead.
 */
object ProofMetrics:

  def of(proof: SCProof): ProofMetrics =
    val seen = mutable.HashSet.empty[Long]
    var raw = 0L
    var shared = 0L
    var maxSeq = 0L

    def sharedSizeOf(e: Expression): Long =
      // A repeat means this whole subtree was counted at its first occurrence, so it is skipped entirely.
      if !seen.add(e.uniqueNumber) then 0L
      else
        e match
          case Application(f, a) => 1L + sharedSizeOf(f) + sharedSizeOf(a)
          case Lambda(_, body) => 1L + sharedSizeOf(body)
          case _ => 1L

    def visit(bot: Sequent): Unit =
      var here = 0L
      bot.left.foreach { e => here += rawSizeOf(e); shared += sharedSizeOf(e) }
      bot.right.foreach { e => here += rawSizeOf(e); shared += sharedSizeOf(e) }
      raw += here
      if here > maxSeq then maxSeq = here

    def walk(steps: IndexedSeq[SCProofStep]): Unit =
      steps.foreach {
        case s: SCSubproof => visit(s.bot); walk(s.sp.steps) // bot once, then the body: `totalLength`'s body + 1
        case s => visit(s.bot)
      }

    walk(proof.steps)
    ProofMetrics(proof.totalLength, raw, shared, maxSeq, proof.imports.length)

  /** Node count of an expression: variables, constants, applications and lambdas each count one. */
  def rawSizeOf(e: Expression): Long = e match
    case Application(f, a) => 1L + rawSizeOf(f) + rawSizeOf(a)
    case Lambda(_, body) => 1L + rawSizeOf(body)
    case _ => 1L
