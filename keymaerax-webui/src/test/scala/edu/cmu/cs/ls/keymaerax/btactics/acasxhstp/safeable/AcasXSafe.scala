/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, LazySequentialInterpreter, SequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.CondCongruence._
import edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.SharedTactics._
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Proves Sect. 3: Safe regions with immediate pilot reaction and infinite advisory duration.
 *
 * Theorem 1: Correctness of implicit safe regions
 * Lemma 1: Equivalence between implicit and explicit region formulation
 * Corollary 1: Correctness of explicit safe regions

 * @see Jean-Baptiste Jeannin et al.: A Formally Verified Hybrid System for Safe Advisories in the Next-Generation
 *      Airborne Collision Avoidance System, STTT.
 *
 * @author Khalil Ghorbal
 * @author Jean-Baptiste Jeannin
 * @author Yanni A. Kouskoulas
 * @author Stefan Mitsch
 * @author Andre Platzer
 */
@SlowTest
class AcasXSafe extends AcasXBase {

  /*** Invariants etc. ***/
  private val invariant = ("( (w= -1 | w=1) & " +
    "      (" +
    "\\forall t \\forall ro \\forall ho" +
    "((0 <= t & t < max(0, w * (dhf - dhd)) / a &" +
    "  ro = rv * t & ho = (w * a) / 2 * t^2 + dhd * t) |" +
    "  (t >= max(0, w * (dhf - dhd)) / a &" +
    "    ro = rv * t & ho = dhf * t - w * max(0, w * (dhf - dhd))^2 / (2*a))" +
    "-> (abs(r - ro) > rp | w * h < w * ho - hp))" +
    "      )) & ( hp>0&rp>=0&rv>=0&a>0 )").asFormula

  private val postcond = "(abs(r)>rp|abs(h)>hp)".asFormula

  private val initDomain = "w*dhd>=w*dhf|w*ao>=a".asFormula

  private lazy val absmax =
    abs('R, "abs(r)".asTerm) &
      abs('R, "abs(h)".asTerm) &
      abs('L, "abs(r-0)".asTerm)

  // Logs all the QE calls, including internal ones
  //private val logQE = QELogger.enableLogging((40,"ACAS X Safe"))

  "ACAS X safe" should "prove use case lemma" in withQE { _ => withDatabase { db =>
    if (containsLemma("nodelay_ucLoLemma")) removeLemma("nodelay_ucLoLemma")

    val ucLoFormula = Imply(invariant, postcond)
    val ucLoTac = implyR('R) & (andL('L)*) &
      allL(Variable("t"), Number(0))('L) &
      allL(Variable("ro"), Number(0))('L) &
      allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
      dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
        EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv") &
        max('L, "max(0,w*(dhf-dhd))".asTerm) & QE & done
      ,
      dT("Absolute value") & absmax & dT("Use case 2") & QE & done
    )

    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)
    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, "nodelay_ucLoLemma")

    // reprove with spoon-feeding interpreter to create extractable tactic
    val proofId = db.createProof(createAcasXProblemFile(ucLoFormula))
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      LazySequentialInterpreter))
    interpreter(ucLoTac, BelleProvable(ProvableSig.startProof(ucLoFormula)))

    val tactic = db.extractTactic(proofId)
    val expectedTactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_uclo.kyt")).mkString)
    tactic shouldBe expectedTactic
  }}

  it should "prove the use case lemma with a parsed Belle tactic" in withQE { _ =>
    if (containsLemma("nodelay_ucLoLemma")) removeLemma("nodelay_ucLoLemma")

    val ucLoFormula = Imply(invariant, postcond)
    val ucLoTac = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_uclo.kyt")).mkString)
    val ucLoLemma = proveBy(ucLoFormula, ucLoTac)

    ucLoLemma shouldBe 'proved
    storeLemma(ucLoLemma, "nodelay_ucLoLemma")
  }

  it should "prove lower bound safe lemma" in withQE { _ =>
    if (containsLemma("nodelay_safeLoLemma")) removeLemma("nodelay_safeLoLemma")

    // Formula from print in Theorem 1
    val safeLemmaFormula = """(w*dhd>=w*dhf|w*ao>=a)&(((w=-1|w=1)&\forall t \forall ro \forall ho (0<=t&t < maxI/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxI/a&ro=rv*t&ho=dhf*t-w*maxI^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&hp>0&rp>=0&rv>=0&a>0)&maxI=max((0,w*(dhf-dhd)))->[{r'=-rv,h'=-dhd,dhd'=ao&w*dhd>=w*dhf|w*ao>=a}](((w=-1|w=1)&\forall t \forall ro \forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp))&hp>0&rp>=0&rv>=0&a>0)""".stripMargin.asFormula

    val safeLemmaTac = dT("lemma") & implyR('R) & (andL('L)*) & solveEnd('R) &
      dT("Before skolem") & ((allR('R) | implyR('R))*) & dT("After skolem") &
      SimplifierV3.simpTac()(1) & dT("Simplified using known facts") & (allR('R)*) &
      //here we'd want to access previously introduced skolem symbol and
      // time introduced by diffSolution;goal 90
      allL(Variable("t"), "t_+t".asTerm)('L) & // t_22+t_23: t_ == t_22, t == t_23
      allL(Variable("ro"), "rv*(t_+t)".asTerm)('L) & // rv*(t_22+t_23)
      dT("Before CUT") &
      cut("0<=t+t_&t+t_<maxI/a|t+t_>=maxI/a".asFormula) & Idioms.<(
      (cutUse, dT("Use Cut") &
        orL('L, "0<=t+t_&t+t_ < maxI/a|t+t_>=maxI/a".asFormula) & Idioms.<(
        dT("Goal 110") & hideL('L, initDomain) &
          allL(Variable("ho"), "w*a/2*(t+t_)^2 + dhd*(t+t_)".asTerm)('L)
          & dT("instantiate ho 1 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(w*a/2*(t+t_)^2+dhd*(t+t_))-hp".asFormula)
          & Idioms.<(
          dT("left of -> 1 Lo") & orR('R) &
            hideR('R, "t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&w*a/2*(t+t_)^2+dhd*(t+t_)=dhf*(t_+t)-w*maxI^2/(2*a)".asFormula) &
            hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & QE & done,
          dT("right of -> 1 Lo") & atomicQE & done
        ) & done,
        dT("final time in straight Lo") &
          allL(Variable("ho"), "dhf*(t+t_) - w*maxI^2/(2*a)".asTerm)('L) &
          dT("instantiate ho 2 Lo") &
          implyL('L, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*(dhf*(t+t_)-w*maxI^2/(2*a))-hp".asFormula)
          & Idioms.<(
          dT("left of -> 2 Lo") & orR('R) &
            hideR('R, "0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&dhf*(t+t_)-w*maxI^2/(2*a)=w*a/2*(t_+t)^2+dhd*(t_+t)".asFormula) &
            hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) & QE & done,
          dT("right of -> 2 Lo") & atomicQE & done
        ) & done
      ) & done
      ) // use
      ,
      (cutShow, dT("Show Cut") & hideL('L, "maxI=max((0,w*(dhf-dhd)))".asFormula) &
        hideL('L, "\\forall ho (0<=t_+t&t_+t < maxI/a&rv*(t_+t)=rv*(t_+t)&ho=w*a/2*(t_+t)^2+dhd*(t_+t)|t_+t>=maxI/a&rv*(t_+t)=rv*(t_+t)&ho=dhf*(t_+t)-w*maxI^2/(2*a)->abs(r-rv*(t_+t))>rp|w*h < w*ho-hp)".asFormula) &
        atomicQE & done) // show
    )

    val safeLemma = proveBy(safeLemmaFormula, safeLemmaTac)
    safeLemma shouldBe 'proved

    storeLemma(safeLemma, "nodelay_safeLoLemma")
  }

  it should "prove Theorem 1: correctness of implicit safe regions" in {
    if (containsLemma("safe_implicit")) removeLemma("safe_implicit")

    runLemmaTest("nodelay_ucLoLemma", "ACAS X safe should prove use case lemma")
    runLemmaTest("nodelay_safeLoLemma", "ACAS X safe should prove lower bound safe lemma")

    beforeEach()
    withQE { _ =>
      /** * Main safe theorem and its tactic ***/
      val safeSeq = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_implicit.kyx")).mkString)

      val safeTac = implyR('R) & (andL('L) *) & loop(invariant)('R) & Idioms.<(
        (initCase, dT("Base case") & prop & done)
        ,
        (useCase, dT("Use case") & andR('R) & Idioms.<(
          cohide2(-1, 1) & implyRi & useLemma("nodelay_ucLoLemma", None) & done,
          (andL('L) *) & closeId & done
        ) & done)
        ,
        (indStep, dT("Step") & composeb('R) & generalize(invariant)('R) & Idioms.<(
          dT("Generalization Holds") & chase('R) & (andL('L)*) & SimplifierV3.simpTac()('R) &  close
          ,
          dT("Generalization Strong Enough") &
            EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) & dT("abbrv2") &

            DifferentialTactics.diffUnpackEvolutionDomainInitially(1) &
            dT("Preparing for safeLoLemma") & hideL(-1) & (andLi *) & implyRi &
            useLemma("nodelay_safeLoLemma", None) & done
          ) /* End indStepLbl */
        )
      )

      val safeTheorem = proveBy(safeSeq, safeTac)
      safeTheorem shouldBe 'proved
      storeLemma(safeTheorem, "safe_implicit")
    }
  }

  it should "prove Lemma 1: equivalence between implicit and explicit region formulation" in withQE { _ =>
    if (containsLemma("safe_equivalence")) removeLemma("safe_equivalence")

    val s = KeYmaeraXProblemParser(io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_equivalence.kyx")).mkString)

    val tactic = implyR('R) & equivR('R) & Idioms.<(
      dT("->") &
        cut("w*dhf>=0 | w*dhf<0".asFormula) & Idioms.<(
          (cutUse, orL('L, "w*dhf>=0 | w*dhf<0".asFormula) & Idioms.<(
            dT("w*dhf>=0") &
            andL('L, "(w*dhf>=0->(-rp<=r&r < -rp-rv*min((0,w*dhd))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&(rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp))&(w*dhf < 0->(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp))".asFormula) &
            hideL('L, "w*dhf < 0->(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)".asFormula) &
            implyL('L, "w*dhf>=0->(-rp<=r&r < -rp-rv*min((0,w*dhd))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&(rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)".asFormula) & Idioms.<(
              hideR('R, "\\forall t \\forall ro \\forall ho (0<=t&t < max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=max((0,w*(dhf-dhd)))/a&ro=rv*t&ho=dhf*t-w*max((0,w*(dhf-dhd)))^2/(2*a)->abs(r-ro)>rp|w*h < w*ho-hp)".asFormula) & closeId,
              (allR('R)*) &
                cut("((r< -rp) | (-rp<=r & r < -rp-rv*min((0,w*dhd))/a) | (-rp-rv*min((0,w*dhd))/a<=r & r<=rp-rv*min((0,w*dhd))/a) | (rp-rv*min((0,w*dhd))/a < r & r<=rp+rv*max((0,w*(dhf-dhd)))/a) | (rp+rv*max((0,w*(dhf-dhd)))/a < r))".asFormula)
                & Idioms.<(
                  (cutUse, EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
                    EqualityTactics.abbrv("min((0,w*dhd))".asTerm, Some(Variable("minA"))) &
                    max('L, "max(0,w*(dhf-dhd))".asTerm) &
                    min('L, "min(0,w*dhd)".asTerm) &
                    abs('R, "abs(r-ro)".asTerm) &
                    orL('L, "r < -rp|-rp<=r&r < -rp-rv*minA/a|-rp-rv*minA/a<=r&r<=rp-rv*minA/a|rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r".asFormula) & Idioms.<(
                      dT("r<-rp") & hideL('L,"((-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp))".asFormula) & QE & done,
                      andL('L, "(-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)".asFormula) &
                        orL('L, "-rp<=r&r < -rp-rv*minA/a|-rp-rv*minA/a<=r&r<=rp-rv*minA/a|rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r".asFormula) & Idioms.<(
                        dT("-> 1:(-rp<=r & r < -rp-rv*minA/a)") &
                          hideL('L, "(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)".asFormula) &
                          implyL('L, "-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp".asFormula) & Idioms.<(
                            hideR('R,"0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)->abs_0>rp|w*h < w*ho-hp".asFormula) & closeId
                            ,
                            implyR('R) & orR('R) &
                              cut("t <= (r+rp)/rv | t > (r+rp)/rv".asFormula) & Idioms.<(
                                (cutUse, orL('L, "t<=(r+rp)/rv|t>(r+rp)/rv".asFormula) & Idioms.<(
                                  dT("t <= (r+rp)/rv") &
                                  hideR('R, "abs_0>rp".asFormula) &
                                    orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) &
                                    onAll(QE) & done
                                  ,
                                  dT("t > (r+rp)/rv") &
                                  hideR('R, "w*h < w*ho-hp".asFormula)  & orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) &
                                    onAll(QE) & done
                                  )
                                )
                                ,
                                (cutShow, QE & done)
                              )
                            )
                          ,
                          hideL('L, "(-rp<=r&r < -rp-rv*minA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)".asFormula) &
                            andL('L, "(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)&(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)".asFormula) &
                            orL('L, "-rp-rv*minA/a<=r&r<=rp-rv*minA/a|rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r".asFormula) & Idioms.<(
                            dT("-> 2: -rp-rv*minA/a<=r&r<=rp-rv*minA/a") &
                              hideL('L, "(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)".asFormula) &
                              implyL('L, "(-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp)".asFormula) & Idioms.<(
                                hideR('R,"0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)->abs_0>rp|w*h < w*ho-hp".asFormula) & closeId & done
                                ,
                                implyR('R) & orR('R) & hideR('R, "abs_0>rp".asFormula) & QE & done
                                )
                              ,
                              hideL('L, "-rp-rv*minA/a<=r&r<=rp-rv*minA/a->w*h < (-minA^2)/(2*a)-hp".asFormula) &
                                andL('L, "(rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp)".asFormula) &
                                orL('L, "rp-rv*minA/a < r&r<=rp+rv*maxA/a|rp+rv*maxA/a < r".asFormula) & Idioms.<(
                                dT("-> 3: rv*minA/a<=r&r<=rp-rv*minA/") &
                                  hideL('L, "rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) &
                                  implyL('L, "rp-rv*minA/a < r&r<=rp+rv*maxA/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp".asFormula) & Idioms.<(
                                    closeId & done,
                                    implyR('R) & cut("t<= (r-rp)/rv | t > (r-rp)/rv".asFormula) & Idioms.<(
                                      (cutUse, orL('L, "t<=(r-rp)/rv|t>(r-rp)/rv".asFormula) & Idioms.<(
                                        orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & onAll(QE) & done
                                        ,
                                        orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & onAll(QE) & done
                                      ))
                                      ,
                                      (cutShow, QE & done)
                                    )
                                  )
                                  ,
                                  dT("-> 4") &
                                    implyL('L, "rp+rv*maxA/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & Idioms.<(
                                      closeId & done,
                                      implyR('R) & cut("t<= (r-rp)/rv | t > (r-rp)/rv".asFormula) & Idioms.<(
                                        (cutUse, orL('L, "t<=(r-rp)/rv|t>(r-rp)/rv".asFormula) & Idioms.<(
                                          orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & onAll(QE) & done
                                          ,
                                          orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & onAll(QE) & done
                                        ))
                                        ,
                                        (cutShow, QE & done)
                                      )
                                    )
                                  )
                              )
                          )
                  )
                )
                ,
                (cutShow, QE & done)
                )
            )
            ,
            dT("w*dhf<0") &
            (andL('L)*) & dT("2nd mark") &
            (allR('R)*) &
            hideL('L, "w*dhf>=0->(-rp<=r&r < -rp-rv*min((0,w*dhd))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp-rv*min((0,w*dhd))/a<=r&r<=rp-rv*min((0,w*dhd))/a->w*h < (-min((0,w*dhd))^2)/(2*a)-hp)&(rp-rv*min((0,w*dhd))/a < r&r<=rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r-rp)^2+w*rv*dhd*(r-rp)-rv^2*hp)&(rp+rv*max((0,w*(dhf-dhd)))/a < r->rv=0|w*rv*h < w*dhf*(r-rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)".asFormula) &
            implyL('L, "w*dhf < 0->(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)".asFormula) & Idioms.<(
              closeId & done
              ,
              cut("(-rp>r)|(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a)|(-rp+rv*max((0,w*(dhf-dhd)))/a<=r)".asFormula) & Idioms.<(
                (cutUse, orL('L, "(-rp>r)|(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a)|(-rp+rv*max((0,w*(dhf-dhd)))/a<=r)".asFormula) & Idioms.<(
                  hideL('L, "(-rp<=r&r < -rp+rv*max((0,w*(dhf-dhd)))/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*max((0,w*(dhf-dhd)))/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*max((0,w*(dhf-dhd)))^2/(2*a)-rv*hp)".asFormula) & QE & done
                  ,
                  implyR('R)  &
                    EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
                    max('L, "max(0,w*(dhf-dhd))".asTerm) &
                    abs('R, "abs(r-ro)".asTerm) &
                    andL('L, "(-rp<=r&r < -rp+rv*maxA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)&(-rp+rv*maxA/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp)".asFormula) &
                    orL('L, "-rp<=r&r < -rp+rv*maxA/a|-rp+rv*maxA/a<=r".asFormula) & Idioms.<(
                      dT("-> 5") &
                      implyL('L,"(-rp<=r&r < -rp+rv*maxA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp)".asFormula) & Idioms.<(
                        closeId & done
                        ,
                        hideL('L, "-rp+rv*maxA/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) &
                          orR('R) &
                          orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & onAll(QE) & done
                      )
                      ,
                      dT("-> 6") &
                      hideL('L, "-rp<=r&r < -rp+rv*maxA/a->w*rv^2*h < a/2*(r+rp)^2+w*rv*dhd*(r+rp)-rv^2*hp".asFormula) &
                      implyL('L, "-rp+rv*maxA/a<=r->rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & Idioms.<(
                        closeId & done
                        ,
                        orL('L, "rv=0&r>rp|w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & Idioms.<(
                          dT("zerocase") &
                          orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) & onAll(QE) & done
                          ,
                          orR('R) & cut("t<= (r+rp)/rv | t > (r+rp)/rv".asFormula) & Idioms.<(
                            (cutUse, orL('L, "t<=(r+rp)/rv|t>(r+rp)/rv".asFormula) & Idioms.<(
                              dT("t<= (r+rp)/rv") & hideR('R, "abs_0>rp".asFormula) &
                                orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) &
                                onAll(QE) & done
                              ,
                              dT("t > (r+rp)/rv") & hideR('R, "w*h < w*ho-hp".asFormula)  &
                                orL('L, "0<=t&t < maxA/a&ro=rv*t&ho=w*a/2*t^2+dhd*t|t>=maxA/a&ro=rv*t&ho=dhf*t-w*maxA^2/(2*a)".asFormula) &
                                onAll(QE) & done
                              )
                            ),
                            (cutShow, QE & done)
                          )
                        )
                      )
                    )
                  )
                ),
                (cutShow, QE & done)
              )
            )
          )
        ),
        (cutShow, cohideR('R, "w*dhf>=0 | w*dhf<0".asFormula) & QE & done)
      )
      ,
      dT("<-") &
      EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxA"))) &
      max('L, "max(0,w*(dhf-dhd))".asTerm) &
      andR('R) & Idioms.<(
        implyR('R) & andR('R) & Idioms.<(
          dT("<- 1") & min('R, "min(0,w*dhd)".asTerm) & implyR('R) & (andL('L)*) & cut("rv=0|rv>0".asFormula) & Idioms.<(
            (cutUse, orL('L, "rv=0|rv>0".asFormula) & Idioms.<(
              dT("<- 1:rv=0") &
                allL(Variable("t"), "0".asTerm)('L) &
                allL(Variable("ro"), "rv*0".asTerm)('L) &
                allL(Variable("ho"), "w*a/2*0^2+dhd*0".asTerm)('L) &
                implyL('L, "0<=0&0 < maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=w*a/2*0^2+dhd*0|0>=maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=dhf*0-w*maxA^2/(2*a)->abs(r-rv*0)>rp|w*h < w*(w*a/2*0^2+dhd*0)-hp".asFormula) & Idioms.<(
                  QE & done
                  ,
                  abs('L, "abs(r-rv*0)".asTerm) & QE & done
                  )
              ,
              dT("<- 1:rv>0") &
                allL(Variable("t"), "(r+rp)/rv".asTerm)('L) &
                allL(Variable("ro"), "rv*((r+rp)/rv)".asTerm)('L) &
                allL(Variable("ho"), "w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)".asTerm)('L) &
                implyL('L, "0<=(r+rp)/rv&(r+rp)/rv < maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)|(r+rp)/rv>=maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=dhf*((r+rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r+rp)/rv))>rp|w*h < w*(w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv))-hp".asFormula) & Idioms.<(
                  QE & done
                  ,
                  abs('L, "abs(r-rv*((r+rp)/rv))".asTerm) & QE & done
                  )
            )),
            (cutShow, QE & done)
          )
          ,
          andR('R) & Idioms.<(
            dT("<- 2") &
            EqualityTactics.abbrv("min((0,w*dhd))".asTerm, Some(Variable("minA"))) &
            min('L, "min((0,w*dhd))".asTerm) &
            implyR('R) & (andL('L)*) & cut("rv=0|rv>0".asFormula) & Idioms.<(
              (cutUse, orL('L, "rv=0|rv>0".asFormula) & Idioms.<(
                dT("<- 2:rv=0") &
                  allL(Variable("t"), "-minA/a".asTerm)('L) &
                  allL(Variable("ro"), "rv*(-minA/a)".asTerm)('L) &
                  allL(Variable("ho"), "w*a/2*(-minA/a)^2+dhd*(-minA/a)".asTerm)('L) &
                  implyL('L, "0<=-minA/a&-minA/a < maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=w*a/2*(-minA/a)^2+dhd*(-minA/a)|-minA/a>=maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=dhf*(-minA/a)-w*maxA^2/(2*a)->abs(r-rv*(-minA/a))>rp|w*h < w*(w*a/2*(-minA/a)^2+dhd*(-minA/a))-hp".asFormula) & Idioms.<(
                    QE & done
                    ,
                    EqualityTactics.abbrv("r-rv*(-minA/a)".asTerm, Some(Variable("absA"))) &
                      abs('L, "abs(absA)".asTerm) & QE & done
                    )
                ,
                dT("<- 2:rv>0") &
                  allL(Variable("t"), "-minA/a".asTerm)('L) &
                  allL(Variable("ro"), "rv*(-minA/a)".asTerm)('L) &
                  allL(Variable("ho"), "w*a/2*(-minA/a)^2+dhd*(-minA/a)".asTerm)('L) &
                  implyL('L, "0<=-minA/a&-minA/a < maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=w*a/2*(-minA/a)^2+dhd*(-minA/a)|-minA/a>=maxA/a&rv*(-minA/a)=rv*(-minA/a)&w*a/2*(-minA/a)^2+dhd*(-minA/a)=dhf*(-minA/a)-w*maxA^2/(2*a)->abs(r-rv*(-minA/a))>rp|w*h < w*(w*a/2*(-minA/a)^2+dhd*(-minA/a))-hp".asFormula) & Idioms.<(
                    QE & done
                    ,
                    EqualityTactics.abbrv("r-rv*(-minA/a)".asTerm, Some(Variable("absA"))) &
                      abs('L, "abs(absA)".asTerm) & QE & done
                    )
                )
              ),
              (cutShow, QE & done)
            )
            ,
            andR('R) & Idioms.<(
              dT("<- 3") & min('R, "min(0,w*dhd)".asTerm) & implyR('R)  & (andL('L)*) &
              cut("rv=0|rv>0".asFormula) & Idioms.<(
                (cutUse, orL('L, "rv=0|rv>0".asFormula) & Idioms.<(
                    dT("<- 3:rv=0") &
                      allL(Variable("t"), "0".asTerm)('L) &
                      allL(Variable("ro"), "rv*0".asTerm)('L) &
                      allL(Variable("ho"), "w*a/2*0^2+dhd*0".asTerm)('L) &
                      implyL('L, "0<=0&0 < maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=w*a/2*0^2+dhd*0|0>=maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=dhf*0-w*maxA^2/(2*a)->abs(r-rv*0)>rp|w*h < w*(w*a/2*0^2+dhd*0)-hp".asFormula) & Idioms.<(
                        QE & done
                        ,
                        abs('L, "abs(r-rv*0)".asTerm) & QE & done
                        )
                    ,
                    dT("<- 3:rv>0") &
                      allL(Variable("t"), "(r-rp)/rv".asTerm)('L) &
                      allL(Variable("ro"), "rv*((r-rp)/rv)".asTerm)('L) &
                      allL(Variable("ho"), "w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)".asTerm)('L) &
                      implyL('L, "0<=(r-rp)/rv&(r-rp)/rv < maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)=w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)|(r-rp)/rv>=maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)=dhf*((r-rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r-rp)/rv))>rp|w*h < w*(w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv))-hp".asFormula) & Idioms.<(
                        QE & done
                        ,
                        abs('L, "abs(r-rv*((r-rp)/rv))".asTerm) & QE & done
                        )
                )),
                (cutShow, QE & done)
              )
              ,
              dT("<- 4") & (andL('L)*) & implyR('R) &
              cut("rv=0|rv>0".asFormula) & Idioms.<(
                (cutUse, orL('L, "rv=0|rv>0".asFormula) & Idioms.<(
                  dT("<- 4:rv=0") &
                    orR('R) & hideR('R, "w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & QE & done
                  ,
                  dT("<- 4:rv>0") &
                    orR('R) & hideR('R, "rv=0".asFormula) &
                    allL(Variable("t"), "(r-rp)/rv".asTerm)('L) &
                    allL(Variable("ro"), "rv*((r-rp)/rv)".asTerm)('L) &
                    allL(Variable("ho"), "dhf*((r-rp)/rv)-w*maxA^2/(2*a)".asTerm)('L) &
                    implyL('L, "0<=(r-rp)/rv&(r-rp)/rv < maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&dhf*((r-rp)/rv)-w*maxA^2/(2*a)=w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)|(r-rp)/rv>=maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&dhf*((r-rp)/rv)-w*maxA^2/(2*a)=dhf*((r-rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r-rp)/rv))>rp|w*h < w*(dhf*((r-rp)/rv)-w*maxA^2/(2*a))-hp".asFormula) & Idioms.<(
                      hideR('R, "w*rv*h < w*dhf*(r-rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & orR('R) &
                        hideR('R, "0<=(r-rp)/rv&(r-rp)/rv < maxA/a&rv*((r-rp)/rv)=rv*((r-rp)/rv)&dhf*((r-rp)/rv)-w*maxA^2/(2*a)=w*a/2*((r-rp)/rv)^2+dhd*((r-rp)/rv)".asFormula) & QE & done
                      ,
                      abs('L, "abs(r-rv*((r-rp)/rv))".asTerm) & QE & done
                      )
                  )
                ),
                (cutShow, QE & done)
              )
            )
          )
        )
        ,
        implyR('R) & andR('R) & Idioms.<(
          dT("<- 5")  & (andL('L)*) &
          cut("rv=0|rv>0".asFormula) & Idioms.<(
            (cutUse, orL('L, "rv=0|rv>0".asFormula) & Idioms.<(
              dT("<- 5:rv=0") &
                allL(Variable("t"), "0".asTerm)('L) &
                allL(Variable("ro"), "rv*0".asTerm)('L) &
                allL(Variable("ho"), "w*a/2*0^2+dhd*0".asTerm)('L) &
                implyL('L, "0<=0&0 < maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=w*a/2*0^2+dhd*0|0>=maxA/a&rv*0=rv*0&w*a/2*0^2+dhd*0=dhf*0-w*maxA^2/(2*a)->abs(r-rv*0)>rp|w*h < w*(w*a/2*0^2+dhd*0)-hp".asFormula) & Idioms.<(
                  QE & done
                  ,
                  abs('L, "abs(r-rv*0)".asTerm) & QE & done
                  )
              ,
              dT("<- 5:rv>0") &
                allL(Variable("t"), "(r+rp)/rv".asTerm)('L) &
                allL(Variable("ro"), "rv*((r+rp)/rv)".asTerm)('L) &
                allL(Variable("ho"), "w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)".asTerm)('L) &
                implyL('L, "0<=(r+rp)/rv&(r+rp)/rv < maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)|(r+rp)/rv>=maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)=dhf*((r+rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r+rp)/rv))>rp|w*h < w*(w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv))-hp".asFormula) & Idioms.<(
                  QE & done
                  ,
                  abs('L, "abs(r-rv*((r+rp)/rv))".asTerm) & QE & done
                  )
            )),
            (cutShow, QE & done)
          )
          ,
          dT("<- 6") & (andL('L)*) & implyR('R) &
          cut("rv=0|rv>0".asFormula) & Idioms.<(
            (cutUse, orL('L, "rv=0|rv>0".asFormula) & Idioms.<(
              dT("<- 6:rv=0") & orR('R)  &
              cut("r>rp|r<=rp".asFormula) & Idioms.<(
                (cutUse, orL('L, "r>rp|r<=rp".asFormula) & Idioms.<(
                  hideR('R, "w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & QE & done
                  ,
                  hideR('R, "rv=0&r>rp".asFormula) &
                  cut("(h+w*maxA^2/(2*a))/dhf>=maxA/a|(h+w*maxA^2/(2*a))/dhf<maxA/a".asFormula) & Idioms.<(
                    (cutUse, orL('L, "(h+w*maxA^2/(2*a))/dhf>=maxA/a|(h+w*maxA^2/(2*a))/dhf<maxA/a".asFormula) & Idioms.<(
                      allL(Variable("t"), "(h+w*maxA^2/(2*a))/dhf".asTerm)('L) &
                      allL(Variable("ro"), "0".asTerm)('L) &
                      allL(Variable("ho"), "h".asTerm)('L) &
                      implyL('L) & Idioms.<(hideR('R,"w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & dT("foo1") & QE, QE)
                      ,
                      allL(Variable("t"), "maxA/a".asTerm)('L) &
                      allL(Variable("ro"), "0".asTerm)('L) &
                      allL(Variable("ho"), "dhf*maxA/a-w*maxA^2/(2*a)".asTerm)('L) &
                        implyL('L) & Idioms.<(hideR('R,"w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & QE, QE)
                      )
                    ),
                    (cutShow, hideR('R,"w*rv*h < w*dhf*(r+rp)-rv*maxA^2/(2*a)-rv*hp".asFormula) & QE & done)
                  )
                )),
                (cutShow, cohideR('Rlast) & QE & done)
              )
              ,
              dT("<- 6:rv>0") & orR('R) & hideR('R, "rv=0&r>rp".asFormula) &
                allL(Variable("t"), "(r+rp)/rv".asTerm)('L) &
                allL(Variable("ro"), "rv*((r+rp)/rv)".asTerm)('L) &
                allL(Variable("ho"), "dhf*((r+rp)/rv)-w*maxA^2/(2*a)".asTerm)('L) &
                implyL('L, "0<=(r+rp)/rv&(r+rp)/rv < maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&dhf*((r+rp)/rv)-w*maxA^2/(2*a)=w*a/2*((r+rp)/rv)^2+dhd*((r+rp)/rv)|(r+rp)/rv>=maxA/a&rv*((r+rp)/rv)=rv*((r+rp)/rv)&dhf*((r+rp)/rv)-w*maxA^2/(2*a)=dhf*((r+rp)/rv)-w*maxA^2/(2*a)->abs(r-rv*((r+rp)/rv))>rp|w*h < w*(dhf*((r+rp)/rv)-w*maxA^2/(2*a))-hp".asFormula) & Idioms.<(
                  QE & done
                  ,
                  abs('L, "abs(r-rv*((r+rp)/rv))".asTerm) & QE & done
              )
            )),
            (cutShow, QE & done)
          )
        )
      )
    )

    val equivalence = proveBy(s, tactic)
    equivalence shouldBe 'proved
    storeLemma(equivalence, "safe_equivalence")
  }

  it should "prove Corollary 1: explicit region safety from implicit region safety and conditional equivalence" in {
    // proof dependency
    // execute other proofs to create lemmas, so that this proof does not fail when run in isolation on
    // a fresh machine
    runLemmaTest("safe_implicit", "ACAS X safe should prove Theorem 1: correctness of implicit safe regions")
    runLemmaTest("safe_equivalence", "ACAS X safe should prove Lemma 1: equivalence between implicit and explicit region formulation")

    beforeEach() // rerun initialization (runTest runs afterEach() at the end)
    withQE {_ =>
      // load lemmas
      val acasximplicit = KeYmaeraXProblemParser( io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_implicit.kyx")).mkString)
      val acasxexplicit = KeYmaeraXProblemParser(io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_explicit.kyx")).mkString)
      val acasximplicitP = getLemma("safe_implicit")
      val implicitExplicitP = getLemma("safe_equivalence")

      // extract formula fragments
      val equivalence = implicitExplicitP.fact.conclusion.succ.head
      val Imply(And(a, w), Equiv(_, i)) = equivalence
      // extract subformulas A()&W(w) -> (Ce(...)<->Ci(...))
      val Imply(And(_, And(_, _)), Box(Loop(_), And(u, _))) = acasximplicit
      val ucLoFact = getLemma("nodelay_ucLoLemma")
      val ucLoLemma = proveBy(Sequent(IndexedSeq(a, w, i), IndexedSeq(u)),
        cut(ucLoFact.fact.conclusion.succ.head) & Idioms.<(
          /*use*/ prop & done,
          /*show*/ cohide(2) & by(ucLoFact)
        )
      )
      ucLoLemma shouldBe 'proved

      val proof: ProvableSig = acasXcongruence(implicitExplicitP.fact, acasximplicitP.fact, ucLoLemma, acasxexplicit, QE)

      println("Proof has " + proof.subgoals.size + " open goals")
      proof shouldBe 'proved
      proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq(acasxexplicit))

      // large lemma evidence, needs stack size -Xss256M
      storeLemma(proof, "safe_explicit")
    }
  }

}
