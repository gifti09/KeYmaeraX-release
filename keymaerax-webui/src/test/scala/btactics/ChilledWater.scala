/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.Find._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Box, Imply}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
  * Chilled water system case study.
  */
@SlowTest
class ChilledWater extends TacticTestBase {

  private val specialNormalize = normalize(andR('R), step('L), step('R))

  def DAcleanup(msg: String): BelleExpr = skip <(
    /* base case */ printIndexed(msg + "b4 QE") & QE & done,
    /* induction: diff*y^2>0 -> [{ode}]diff*y^2>0 */ printIndexed(msg + "b4 diffInd") &
    diffInd()(1, 1::Nil) & QE & done // formula of the form lhs -> rhs, 1::Nil traverses to rhs
    )

  /* DA depending on the states of valve and load, diff is what we're trying to prove is
     positive (e.g., Tl-Tw) */
  def DAchilled(valve: Boolean, load: Option[Boolean], diff: String) = ((valve, load) match {
    case (true, _) =>
      DA("{y'=(r()/2)*y+0}".asDifferentialProgram, s"($diff)*y^2>0".asFormula)(1)
    case (false, Some(false)) =>
      DA("{y'=r()*y+0}".asDifferentialProgram, s"($diff)*y^2>0".asFormula)(1)
    case (false, Some(true)) =>
      DA("{y'=r()*y+0}".asDifferentialProgram, s"($diff)*y^2>0".asFormula)(1)
    // no other case expected to occur
  }) & DAcleanup(s"After DA (load=$load, valve=$valve, diff=$diff)")

  /* Case [ctrl;ode]Tw<Tl */
  def twLessTl = printIndexed("case split on model non-det. choices") <(
    /*v:=1;Tw:=a()*/ DAchilled(valve=true, load=None, "Tl-Tw") & done,
    /* ?l=0;v:=0; */ DAchilled(valve=false, load=Some(false), "Tl-Tw") & done,
    /* ?v=1;l:=1; */ DAchilled(valve=true, load=Some(true), "Tl-Tw") & done,
    /* l:=0; split v=1|v=0 */
    orL(FindL(0, Some("v=1|v=0".asFormula))) <(
      /* v=1 */ DAchilled(valve=true, load=Some(false), "Tl-Tw") & done,
      /* v=0 */ DAchilled(valve=false, load=Some(false), "Tl-Tw") & done
      )
    )

  /* Case [ctrl;ode]Tl<Tlu(), reduces to Tw<Tl whenever possible */
  def tlLessTlu = printIndexed("case split on model non-det. choices") <(
    /* v:=1;Tw:=a(), here we need to actually exploit h()/r()+a()<Tlu() */
    diffInvariant("Tw=a()".asFormula)(1) & DAchilled(valve=true, load=None, "Tlu()-Tl") & done,
    /* ?l=0;v:=0; */
    diffCut("Tw<Tl".asFormula)(1) <(
      /* use cut */ diffInd()(1) & done,
      /* show cut */ DAchilled(valve=false, load=Some(false), "Tl-Tw") & done //@note now we know sign of Tl' plus Tl<Tlu initially
      ),
    /* ?v=1;l:=0; */
    diffInvariant("Tw=a()".asFormula)(1) & DAchilled(valve=true, load=Some(false), "Tlu()-Tl") & done,
    /* l:=0; */
    orL(FindL(0, Some("v=1|v=0".asFormula))) <(
      /* v=1 */
      diffInvariant("Tw=a()".asFormula)(1) & DAchilled(valve=true, load=Some(false), "Tlu()-Tl") & done,
      /* v=0 */
      diffCut("Tw<Tl".asFormula)(1) <(
        /* use cut */ diffInd()(1) & done,
        /* show cut */ DAchilled(valve=false, load=Some(false), "Tl-Tw") & done
        )
      )
    )

  /* Case [ctrl;ode]a()<=Tw */
  def aLessEqualTw = skip <(
    /* v:=1;Tw:=a; */ diffInvariant("Tw=a()".asFormula)(1) & diffWeaken(1) & QE & done,
    /* ?l=0;v:=0; */ diffCut("Tw<Tl".asFormula, "a()<=Tw".asFormula)(1) <(
    diffWeaken(1) & QE & done,
    DAchilled(valve=false, load=Some(false), "Tl-Tw") & done,
    diffInd()(1) & done
    ),
    /* ?v=1;l:=1; */ diffInvariant("Tw=a()".asFormula)(1) & diffWeaken(1) & QE & done,
    /* l:=0; */ diffCut("Tw<Tl".asFormula, "a()<=Tw".asFormula)(1) <(
    diffWeaken(1) & QE & done,
    orL(FindL(0, Some("v=1|v=0".asFormula))) <(
      DAchilled(valve=true, load=Some(false), "Tl-Tw") & done,
      DAchilled(valve=false, load=Some(false), "Tl-Tw") & done
      ),
    diffInd()(1) & done
    )
    )

  def propRest = skip <(
    diffInvariant("Tw=a()".asFormula)(1),
    skip, //@note evolution domain already strong enough without additional diff. cut
    diffInvariant("Tw=a()".asFormula)(1),
    orL(FindL(0, Some("v=1|v=0".asFormula))) <(
      diffInvariant("Tw=a()".asFormula)(1),
      skip //@note evolution domain already strong enough without additional diff. cut
      )
    ) & OnAll(diffWeaken(1) & QE) & done

  "Model 0" should "be provable" in withMathematica { implicit qeTool =>
    //val s = KeYmaeraXProblemParser(scala.io.Source.fromFile("/path/to/file").getLines().mkString)
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/chilledwater/chilled-m0.kyx"))
    val inv = """(Tw < Tl) &
                |    (Tl < Tlu() &
                |    a() <= Tw &                  /* needed for DA in model branch v:=1;Tw:=a() */
                |    (l=1 -> v=1) &              /* If the load is on, the valve is open.        */
                |    (v=0 -> l=0) &              /* If the valve is closed, the load is off.     */
                |    (l=0 | l=1) &
                |    (v=1 | v=0) &
                |    (v=1 -> Tw=a()))""".stripMargin.asFormula

    val tactic = implyR('_) & (andL('_)*) & printIndexed("implyR then andL") & loop(inv)(1) & printIndexed("After loop") <(
      QE & done,
      QE & done,
      boxAnd(1) & andR(1) <(
        /* Tw < Tl */
        chase(1) & specialNormalize & twLessTl & done,
        boxAnd(1) & andR(1) <(
          /* Tl < Tlu() */
          chase(1) & specialNormalize & tlLessTlu & done,
          boxAnd(1) & andR(1) <(
            /* a() <= Tw */
            chase(1) & specialNormalize & aLessEqualTw & done,
            /* all the propositional minutia */
            chase(1) & specialNormalize & propRest & done
            )
          )
        )
      )

    proveBy(s, tactic) shouldBe 'proved
  }

  "Model 1" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/chilledwater/chilled-m1.kyx"))
    val inv = """(Tw < Tl) &
                |    (Tl < Tlu() &
                |    a() <= Tw &                  /* needed for DA in model branch v:=1;Tw:=a() */
                |    (l=0 | l=1) &
                |    (v=1 | v=0) &
                |    (v=1 -> Tw=a()))""".stripMargin.asFormula

    val tactic = implyR('_) & (andL('_)*) & printIndexed("implyR then andL") & loop(inv)(1) & printIndexed("After loop") <(
      QE & done,
      QE & done,
      // reduce the proof to the proof of Model 0
      boxAnd(1) & andR(1) <(
        /* Tw < Tl */
        chase(1) & specialNormalize <(
          skip,
          skip,
          /* new branch */
          diffCut("Tw<Tl".asFormula)(1) <(
            /* use cut */ diffWeaken(1) & QE & done,
            /* show cut */ DAchilled(valve=false, load=Some(true), "Tl-Tw") & done
            ) & done,
          skip,
          skip
          ) & twLessTl & done,
        boxAnd(1) & andR(1) <(
          /* Tl < Tlu() */
          chase(1) & specialNormalize <(
            skip,
            skip,
            /* new branch */
            diffCut("Tw<Tl".asFormula)(1) <(
              /* use cut */ diffInvariant("Tl<Tlu()-h()*(e()-t)".asFormula)(1) & diffWeaken(1) & QE & done,
              /* show cut */ DAchilled(valve=false, load=Some(true), "Tl-Tw") & done
              ) & done,
            skip,
            skip
          ) & tlLessTlu & done,
          boxAnd(1) & andR(1) <(
            /* a() <= Tw */
            chase(1) & specialNormalize <(
              skip,
              skip,
              /* new branch */
              diffCut("Tw<Tl".asFormula, "a()<=Tw".asFormula)(1) <(
                diffWeaken(1) & QE & done,
                DAchilled(valve=false, load=Some(true), "Tl-Tw") & done,
                diffInd()(1) & done
                ),
              skip,
              skip
              ) & aLessEqualTw & done,
            /* all the propositional minutia */
            chase(1) & specialNormalize <(
              skip,
              skip,
              /* new branch */
              diffWeaken(1) & QE & done,
              skip,
              skip
              ) & propRest & done
            )
          )
        )
      )

    proveBy(s, tactic) shouldBe 'proved
  }

}

