/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Differential Dynamic Logic expression pretty printing.
  * @author Andre Platzer
  * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
  * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
  * @note Code Review 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

/**
  * A pretty printer for differential dynamic logic is a function from Expressions to Strings.
  * This object manages the default pretty printer that KeYmaera X uses in [[Expression.prettyString]].
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.PrettyPrinter]]
  * @see [[Expression.prettyString]]
  */
object PrettyPrinter extends (Expression => String) {
  /** Pretty-print the given expression using printer() */
  def apply(expr: Expression): String = printer(expr)

  /**
    * A pretty printer for differential dynamic logic is a function from Expressions to Strings.
    */
  type PrettyPrinter = (Expression => String)

  /* @note mutable state for switching out default pretty printers, which defaults to just printing class names as does super.toString */
  private[this] var pp: PrettyPrinter = (e => e.getClass.getName)

  def printer: PrettyPrinter = pp

  /**
    * Set a new pretty printer to be used from now on.
    * @param printer the pretty-printer to use in KeYmaera X from now on.
    */
  def setPrinter(printer: PrettyPrinter) = {pp = printer}
}
