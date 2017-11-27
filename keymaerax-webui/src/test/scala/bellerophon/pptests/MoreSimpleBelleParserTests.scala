package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
  * These are probably unnecessary now that SimpleBelleParserTests is  around, but they are very fast so additional
  * coverage can't hurt.
  * @author Nathan Fulton
  */
class MoreSimpleBelleParserTests extends TacticTestBase {
//  @deprecated("Switch to BelleParser", "4.2b1")
//  private def oldParser(s: String): BelleExpr = BTacticParser(s).get

  private def newParser(s: String): BelleExpr = BelleParser(s)

  /** The parsing function to use for these test cases. */
  private val parser : String => BelleExpr = newParser

  "The Bellerophon Tactics Parser" should "parse nil & nil" in {
    val result = parser("nil & nil").asInstanceOf[SeqTactic]
    val expected = SeqTactic(Idioms.nil, Idioms.nil)
    result.left shouldBe expected.left
    result.right shouldBe expected.right
  }

  it should "parser nil < (nil, nil, nil)" in {
    val result = parser("nil < (nil, nil, nil)").asInstanceOf[SeqTactic]
    val expected = SeqTactic(Idioms.nil, BranchTactic(Seq(Idioms.nil, Idioms.nil, Idioms.nil)))
    result.left shouldBe expected.left
    result.right.asInstanceOf[BranchTactic].children
      .zip(expected.right.asInstanceOf[BranchTactic].children)
      .map(x => x._1 shouldBe x._2)
  }

  it should "parse expression arguments with {} in them" in {
    parser("loop({`[{x' = v, v' = -b}]x <= m`}, 1)") //ok
  }

  it should "parse partials and built-ins" in {
    val result = parser("partial(implyR)")
    result.isInstanceOf[PartialTactic] shouldBe true
    result.asInstanceOf[PartialTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse post-fix partials and built-ins" in {
    val result = parser("implyR partial")
    result.isInstanceOf[PartialTactic] shouldBe true
    result.asInstanceOf[PartialTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse either" in {
    val result = parser("nil | implyR").asInstanceOf[EitherTactic]
    result.left.prettyString shouldBe  """nil"""
    result.right.prettyString shouldBe "implyR"
  }

  it should "parse *" in {
    val result = parser("implyR*")
    result.isInstanceOf[SaturateTactic] shouldBe true
    result.asInstanceOf[SaturateTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse *@" in {
    val result = parser("implyR*")
    result.isInstanceOf[SaturateTactic] shouldBe true
    result.asInstanceOf[SaturateTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse positional tactics" in {
    val tactic = parser("implyR(1)")
    tactic.isInstanceOf[AppliedPositionTactic] shouldBe true
    val apt = tactic.asInstanceOf[AppliedPositionTactic]
    apt.locator.isInstanceOf[Fixed] shouldBe true
    apt.positionTactic.prettyString shouldBe "implyR"
  }

  it should "parse formula tactics" in {
    val tactic = parser("loop({`v >= 0`})")
    tactic.isInstanceOf[DependentPositionTactic] shouldBe true
    val dpt = tactic.asInstanceOf[DependentPositionTactic]
  }

  it should "parse j(x) as a term or a formula depending on ArgInfo." in {
    parser("loop({`j(x)`})") shouldBe TactixLibrary.loop("j(x)".asFormula)
    parser("allL({`j(x)`})") shouldBe TactixLibrary.allL("j(x)".asTerm)
  }

  it should "parse exact matching search" in {
    parser("implyR('R=={`x>0->x>=0`})") shouldBe TactixLibrary.implyR('R, "x>0->x>=0".asFormula)
    parser("andL('L=={`x>0&x>=0`})") shouldBe TactixLibrary.andL('L, "x>0&x>=0".asFormula)
    parser("absExp('L=={`abs(x*y)`})") shouldBe TactixLibrary.abs('L, "abs(x*y)".asTerm)
    parser("andL('_=={`x>0&x>=0`})") shouldBe TactixLibrary.andL('_, "x>0&x>=0".asFormula)
  }

  it should "parse unifiable matching search" in {
    parser("implyR('R~={`x>0->x>=0`})") shouldBe TactixLibrary.implyR('Rlike, "x>0->x>=0".asFormula)
    parser("andL('L~={`x>0&x>=0`})") shouldBe TactixLibrary.andL('Llike, "x>0&x>=0".asFormula)
    parser("absExp('L~={`abs(x)`})") shouldBe TactixLibrary.abs('Llike, "abs(x)".asTerm)
  }

  it should "parse fancy dG" in {
    parser("dG({`y' = 0`})") shouldBe TactixLibrary.dG("y'=0".asDifferentialProgram, None)
    parser("dG({`y' = 0`}, {`1=1`})") shouldBe TactixLibrary.dG("y'=0".asDifferentialProgram, Some("1=1".asFormula))
    parser("dG({`y' = 0`}, {`1=1`},1)") shouldBe TactixLibrary.dG("y'=0".asDifferentialProgram, Some("1=1".asFormula))(1)
  }

  //@todo move this.
  it should "print fancy dG and round trip" in {
    val t = TactixLibrary.dG("y'=0".asDifferentialProgram, Some("1=1".asFormula))(1)
    val result = t.prettyString
    parser(result) shouldBe t
    result shouldBe "dG({`{y'=0}`},{`1=1`},1)"
  }

  "Propositional Examples" should "close p() -> p()" in {
    val tactic = parser("implyR(1) & closeId")
//    val tactic = ExposedTacticsLibrary.tactics("implyR") & ExposedTacticsLibrary.tactics("TrivialCloser")
    val value = BelleProvable(ProvableSig.startProof("p() -> p()".asFormula))
    val result = BelleInterpreter(tactic, value)
    result match {
      case BelleProvable(resultingProvable, _) => resultingProvable.isProved shouldBe true
      case _ => throw new Exception("Expected a BelleProvable.")
    }
  }
}
