package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser._
import edu.cmu.cs.ls.keymaerax.btactics.{DifferentialTactics, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Parser test cases that arise from known bugs.
  * @note When a bug is well-understood it might make sense to move tests out of this suite and into a suite that
  *       associated with the original cause of the bug. For that reason this suite might end up temporarily empty.
  *       None-the-less, please leave this file around as the default place to reproduce of parser bugs until the
  *       BelleParser stabilizes.
  * @author Nathan Fulton
  */
class BelleParserRegressionTest extends TacticTestBase {
  "expression pattern" should "match multi-expression-argument input" in {
    "{`1=1`}, {`1=2`}, 1)" match {
      case EXPRESSION2.startPattern(e) => e shouldBe "{`1=1`}"
      case _ => assert(false, "Expected EXPRESSION2 to match the current input")
    }
  }

  "diffGhost" should "parse" in {
    BelleParser("diffGhost({`t`}, {`0`}, {`1`}, {`2`}, 1)") shouldBe DifferentialTactics.diffGhost("{t'=0*t+1}".asDifferentialProgram, "2".asTerm)(1)
  }

  "DG" should "parse" in {
    val parseResult = BelleParser("DGTactic({`t`}, {`0`}, {`1`}, 1)")
    val expected = DifferentialTactics.DG("{t'=0*t+1}".asDifferentialProgram)(1)

    parseResult shouldBe expected
  }
}
