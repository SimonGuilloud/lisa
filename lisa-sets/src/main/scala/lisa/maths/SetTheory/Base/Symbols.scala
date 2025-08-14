package lisa.maths.SetTheory.Base

/**
  * This file defines the most common variable symbols (x, y, z, etc.) and their
  * types for a consistent use through the standard library.
  *
  * Symbols defined here must have an unambiguous and widely accepted meaning.
  */
object Symbols extends lisa.Main {

  /** Variable symbols */
  val x, y, z: Variable[Set] = variable[Set]
  val a, b, c, d: Variable[Set] = variable[Set]

  /** Sets */
  val A, B, C, D: Variable[Set] = variable[Set]
  val X, Y: Variable[Set] = variable[Set]

  /** Function symbols */
  val f, g, h: Variable[Set] = variable[Set]

  /** Class-function symbols. Must be capitalized. */
  val F: Variable[Set >>: Set] = variable[Set >>: Set]

  /** Predicate (class) symbols */
  val P, φ: Variable[Set >>: Prop] = variable[Set >>: Prop]

}

