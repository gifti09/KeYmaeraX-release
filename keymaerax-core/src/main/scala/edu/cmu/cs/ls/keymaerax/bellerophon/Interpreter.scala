package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
  * Interpreter for Bellerophon tactic expressions that transforms [[BelleValue Bellerophon values]] using
  * [[BelleExpr Bellerophon tactic language expressions]] to ultimately produce [[ProvableSig]].
  * {{{
  *   Interpreter : BelleExpr * BelleValue => BelleValue
  * }}}
 *
  * @author Nathan Fulton
  * @see [[SequentialInterpreter]]
  */
trait Interpreter {
  /** Returns the result of applying tactic `expr` to the proof value `v` (usually a provable). */
  def apply(expr: BelleExpr, v: BelleValue): BelleValue

  /** Stops the interpreter and kills all its tactic executions. */
  def kill(): Unit
}

/**
  * Listeners for input/output results during the [[Interpreter interpretation]] of Bellerophon tactic expressions.
  */
trait IOListener {
  def begin(input: BelleValue, expr: BelleExpr): Unit
  def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue,BelleThrowable]): Unit
  def kill(): Unit
}