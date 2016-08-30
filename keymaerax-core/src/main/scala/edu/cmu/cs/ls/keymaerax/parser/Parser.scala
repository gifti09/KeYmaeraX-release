/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Parser interface for KeYmaera X.
 * Provides a parser to read string and file inputs with differential dynamic logic.
 * A parser is essentially a function from input string to differential dynamic logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]].
 * {{{
 *     Parser: String => Expression
 * }}}
 * @author Andre Platzer
 */
trait Parser extends (String => Expression) {

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  def apply(input: String): Expression

  /** Parse the input string in the concrete syntax as a differential dynamic logic term */
  val termParser: (String => Term)

  /** Parse the input string in the concrete syntax as a differential dynamic logic formula */
  val formulaParser: (String => Formula)

  /** Parse the input string in the concrete syntax as a differential dynamic logic program */
  val programParser: (String => Program)

  /** Parse the input string in the concrete syntax as a differential dynamic logic differential program */
  val differentialProgramParser: (String => DifferentialProgram)

  /** A pretty-printer that can write the output that this parser reads */
  val printer: PrettyPrinter

}
