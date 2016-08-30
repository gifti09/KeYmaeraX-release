/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.Map

/**
 * Z3 quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Z3 extends ToolBase("Z3") with QETool with DiffSolutionTool with CounterExampleTool {
  private val z3 = new Z3Solver

  override def init(config: Map[String,String]) = {
    initialized = true
  }

  override def qeEvidence(formula: Formula): (Formula, Evidence) = {
    require(isInitialized, "Z3 needs to be initialized before use")
    z3.qeEvidence(formula)
  }

  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable,
                       iv: Predef.Map[Variable, Variable]): Option[Formula] = {
    throw new Exception("Solving differential equations not supported by Z3")
  }

  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Term]] = {
    throw new Exception("Counterexample generation not yet implemented with Z3")
  }

  override def restart() = ???

  override def shutdown() = {
    initialized = false
  }
}
