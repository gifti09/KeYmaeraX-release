package cbcps

import java.io.{File, FileInputStream}

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentPositionTactic, Find, OnAll}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, _}
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ParserFactory._

import scala.collection.immutable.Seq
import scala.collection.mutable

/**
  * Created by andim on 13.10.2016.
  */
class PerformanceTest extends TacticTestBase {

  def baseTactic: BelleExpr = QE

  def useTactic: BelleExpr = QE

  def stepTactic: BelleExpr = master() // chase(1) & normalize & master()

  def sideTactic: BelleExpr = master()

  /*=====================================*
   * Running Example 1 - Traffic Control *
   *  INCOMPLETE                         *
   *=====================================*/

  behavior of "Component-based Traffic Networks"

  ignore should "prove Merge Component" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\1-traffic\\merge.kyx")))

    val invariant =
      """t>=0
        | & 0<=road & road<=1
        |	& l1 <= t * MAXIN1
        |	& l2 <= t * MAXIN2
        | & 0<=out & out<=MAXOUT""".stripMargin.asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  ignore should "prove Split Component" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\1-traffic\\split.kyx")))

    val invariant =
      """t>=0 & 0<=road & road<=1 & l<= t*(MAXIN-MAXOUT2)""".stripMargin.asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  ignore should "prove Traffic Light Component" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\1-traffic\\trafficlight.kyx")))

    val invariant =
      """tc<=Tc & go*(go-1) = 0 & t>=0 & tc>=0
        | & Tc>0 & T>0 & 0<=MAXIN & 0<=MAXOUT
        |	& l <= t * (2*in-out)/2+Tc*(out/2)
        |	& l + (Tc-tc)*(in-go*out) <= (t+Tc-tc) * (2*in-out)/2+Tc*(out/2)
        |	& ( (go = 0) -> l + (Tc-tc)*(in) + (Tc)*(in-out) <= (t+(Tc-tc+Tc))*(2*in-out)/2+Tc*(out/2) )
        | & c>= T*MAXIN-(T-Tc)/2*MAXOUT & c>= Tc*MAXIN
        | & l<= t*MAXIN-(t-Tc)/2*MAXOUT & l>=0 & l<= Tc*MAXIN""".stripMargin.asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)('R) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  /*===========================================================*
   * Running Example 2a - Automated Robot Cruise Control (pt2) *
   *===========================================================*/

  behavior of "Component-based Automated Robot Cruise Control"

  ignore should "prove Automated Controller Component" in withMathematica { implicit tool =>
    val ac: Component = new Component("Automated Controller",
      """ sAcTr:=*;
        | ?(0<=sAcTr & sAcTr<=S & abs(sAcTr-sAc)<=deltaS);
      """.stripMargin.asProgram)
    val acI: Interface = Interface.SinglePortInterface(mutable.LinkedHashMap("sAc".asVariable -> "0<=sAc & sAc<=S".asFormula), mutable.LinkedHashMap("sAcTr".asVariable -> "0<=sAcTr & sAcTr<=S".asFormula))
    val acCtr: DelayContract = new DelayContract(ac, acI,
      """sAcTr=0
        |& S>0
        |& deltaS>0
      """.stripMargin.asFormula,
      "true".asFormula,
      "0<=sAcTr & sAcTr<=S".asFormula)

    acCtr.verifyBaseCase(baseTactic)
    acCtr.verifyUseCase(useTactic)
    acCtr.verifyStep(stepTactic)

    acCtr shouldBe 'verified

    Contract.save(acCtr, "pt2-controller-automated.cbcps")
  }

  ignore should "prove Actuator Component" in withMathematica { implicit tool =>
    val eps = Globals.eps.name
    val act: Component = new Component("Actuator",
      s" aAct:=(sActTr-sAct)/$eps;".asProgram,
      new ODESystem("sAct'=aAct".asDifferentialProgram))
    val actI: Interface = Interface.SinglePortInterface(mutable.LinkedHashMap("sActTr".asVariable -> "0<=sActTr & sActTr<=S".asFormula), mutable.LinkedHashMap("sAct".asVariable -> "0<=sAct & sAct<=S".asFormula))
    val actCtr: DelayContract = new DelayContract(act, actI,
      s"""0<=sAct & sAct<=S
         |& S>0
         |& $eps>0
         |& sActTr=0
      """.stripMargin.asFormula,
      "0<=sAct & sAct<=S".asFormula,
      "0<=sAct & sAct<=S & 0<=sActTr & sActTr<=S & S>0 & ep>0".asFormula)

    println("CTR: " + actCtr.contract())

    actCtr.verifyBaseCase(baseTactic)
    actCtr.verifyUseCase(useTactic)
    actCtr.verifyStep(stepTactic)

    actCtr shouldBe 'verified

    Contract.save(actCtr, "pt2-actuator.cbcps")
  }

  ignore should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val acCtr: Contract = Contract.load("pt2-controller-automated.cbcps")
    val actCtr: Contract = Contract.load("pt2-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sAc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sAcTr".asVariable)
    )

    //CPO
    acCtr.cpo(actCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt2-automated-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    acCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt2-controller-automated-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    actCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt2-actuator-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  ignore should "prove Composition" in withMathematica { implicit tool =>
    val acCtr: Contract = Contract.load("pt2-controller-automated.cbcps")
    val actCtr: Contract = Contract.load("pt2-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sAc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sAcTr".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](acCtr.cpo(actCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt2-automated-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val acSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](acCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt2-controller-automated-side-" + v).get
    }
    }.toSeq: _*)
    val actSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](actCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt2-actuator-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(acCtr, actCtr, X, cpo, acSc, actSc)

    sysCtr shouldBe 'verified
    //    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic Automated Robot Cruise Control"

  ignore should "prove Automated System" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\AutoMono.kyx")))
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\AutoMono.kyx")))

    val invariant = "0<=sAct&sAct<=S & sAc=sAct & sActTr=sAcTr & 0<=sAcTr&sAcTr<=S".asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  behavior of "Expert Automated Robot Cruise Control"

  ignore should "prove Automated System" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\AutoExpert.kyx")))
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\AutoExpert.kyx")))

    val invariant = "0<=sAct&sAct<=S & sAc=sAct & sActTr=sAcTr & 0<=sAcTr&sAcTr<=S".asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }


  /*========================================================*
   * Running Example 2b - Guided Robot Cruise Control (pt2) *
   *========================================================*/

  behavior of "Component-based Guided Robot Cruise Control"

  ignore should "prove Guided Controller Component" in withMathematica { implicit tool =>
    val gc: Component = new Component("Guided Controller",
      """ {
        |   { ?(sGcUsr-sGc >= deltaS); sGcTr:=sGc+deltaS; } /* user velocity is too fast -> use current+delta */
        |  ++
        |   { ?(sGc-sGcUsr >= deltaS); sGcTr:=sGc-deltaS; } /* user velocity is too slow -> use current-delta */
        |  ++
        |   { ?(abs(sGcUsr-sGc) < deltaS); sGcTr:=sGcUsr; }  /* user velocity is ok -> use it */
        | }""".stripMargin.asProgram)
    val gcI: Interface = Interface.SinglePortInterface(mutable.LinkedHashMap("sGcUsr".asVariable -> "0<=sGcUsr & sGcUsr<=S".asFormula, "sGc".asVariable -> "0<=sGc & sGc<=S".asFormula),
      mutable.LinkedHashMap("sGcTr".asVariable -> "0<=sGcTr & sGcTr<=S".asFormula))
    val gcCtr: DelayContract = new DelayContract(gc, gcI,
      """ sGcTr=0
        | & sGcUsr=0
        | & 0<=sGc & sGc<=S
        | & ep > 0
        | & S > 0
        | & deltaS > 0""".stripMargin.asFormula,
      "true".asFormula,
      "0<=sGcTr & sGcTr<=S & 0<=sGcUsr & sGcUsr<=S & sGcUsr<=S & 0<=sGc & sGc<=S & S>0 & deltaS>0 & ep > 0".asFormula)

    println("CTR: " + gcCtr.contract())

    gcCtr.verifyBaseCase(baseTactic & print("bc done?"))
    gcCtr.verifyUseCase(useTactic & print("uc done?"))
    gcCtr.verifyStep(stepTactic & print("step done?"))

    gcCtr shouldBe 'verified

    Contract.save(gcCtr, "pt2-controller-guided.cbcps")
  }

  ignore should "reuse Actuator Component" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_rbc.kyx")))
    val actCtr: Contract = Contract.load("pt2-actuator.cbcps")

    actCtr shouldBe 'verified
  }

  ignore should "prove new CPO and Sideconditions" in withMathematica { implicit tool =>
    val gcCtr: Contract = Contract.load("pt2-controller-guided.cbcps")
    val actCtr: Contract = Contract.load("pt2-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sGc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sGcTr".asVariable)
    )

    //CPO
    gcCtr.cpo(actCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt2-guided-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    gcCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt2-controller-guided-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    //    actCtr.sideConditions().foreach { case (v, f: Formula) => {
    //      val p = ProofHelper.verify(f, master(), Some("pt2-actuator-side-" + v))
    //      p shouldBe 'nonEmpty
    //      v -> p
    //    }
    //    }
  }

  ignore should "prove Composition" in withMathematica { implicit tool =>
    val gcCtr: Contract = Contract.load("pt2-controller-guided.cbcps")
    val actCtr: Contract = Contract.load("pt2-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sGc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sGcTr".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](gcCtr.cpo(actCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt2-guided-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val acSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](gcCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt2-controller-guided-side-" + v).get
    }
    }.toSeq: _*)
    val actSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](actCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt2-actuator-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(gcCtr, actCtr, X, cpo, acSc, actSc)

    sysCtr shouldBe 'verified
    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic Guided Robot Cruise Control"

  ignore should "prove Guided System" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\GuidedMono.kyx")))
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\GuidedMono.kyx")))

    val invariant = "0<=sAct&sAct<=S & sGc=sAct & sActTr=sGcTr & 0<=sGcTr&sGcTr<=S & 0<=sGcUsr & sGcUsr<=S".asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }


  behavior of "Expert Guided Robot Cruise Control"

  ignore should "prove Guided System" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\GuidedMono.kyx")))
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\GuidedExpert.kyx")))

    val invariant = "0<=sAct&sAct<=S & sGc=sAct & sActTr=sGcTr & 0<=sGcTr&sGcTr<=S & 0<=sGcUsr & sGcUsr<=S".asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  /*====================================================*
   * Running Example 3 - Robot Obstacle Avoidance (pt3) *
   *====================================================*/

  //Mathematica
  behavior of "Component-based Robot Obstacle Avoidance"

  it should "prove Obstacle-Remote Component" in withMathematica { implicit tool =>
    val t = Globals.runT
    val obs = new Component("Obstacle-Remote", "d:=*;?abs(d-d0)<=D;so:=*;?(0<=so&so<=S);".asProgram, ODESystem("po'=so".asDifferentialProgram))
    val obsI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("d".asVariable) -> "abs(d-d0)<=D".asFormula, Seq("po".asVariable) -> s"abs(po-po0)<=S*$t".asFormula),
      mutable.LinkedHashMap(Seq("d".asVariable) -> Seq("d0".asVariable), Seq("po".asVariable) -> Seq("po0".asVariable)))
    val obsCtr = new DelayContract(obs, obsI, And(Globals.initTOld, "D>=0 & d=d0 & S>=0 & po=po0 & so=0".asFormula), True, s"D>=0 & S>=0 & 0<=so&so<=S & abs(d-d0)<=D & abs(po-po0)<=S*$t".asFormula)

    obsCtr.verifyBaseCase(baseTactic)
    obsCtr.verifyUseCase(useTactic)
    obsCtr.verifyStep(stepTactic)

    obsCtr shouldBe 'verified

    Contract.save(obsCtr, "pt3-obstacle-remote.cbcps")
  }

  it should "prove Robot Component" in withMathematica { implicit tool =>
    val t = Globals.runT
    val rob = new Component("Robot", "{?abs(poIn-pr)>dIn*ep+S*ep;sr:=dIn;} ++ {?abs(poIn-pr)<=dIn*ep+S*ep;sr:=0;}".asProgram, ODESystem("pr'=sr".asDifferentialProgram))
    val robI = new Interface(
      mutable.LinkedHashMap(Seq("dIn".asVariable) -> "abs(dIn-dIn0)<=D".asFormula, Seq("poIn".asVariable) -> s"abs(poIn-poIn0)<=S*$t".asFormula),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("dIn".asVariable) -> Seq("dIn0".asVariable), Seq("poIn".asVariable) -> Seq("poIn0".asVariable), Seq("pr".asVariable) -> Seq("pr0".asVariable)))
    val robCtr = new DelayContract(rob, robI,
      And(Globals.initTOld, "ep>0 & D>=0 & dIn=dIn0 & S>=0 & poIn=poIn0 & sr=0".asFormula),
      "sr>0 -> poIn!=pr".asFormula,
      s"ep>0 & D>=0 & S>=0 & abs(dIn-dIn0)<=D & abs(poIn-poIn0)<=S*$t & (sr>0 -> poIn!=pr)".asFormula)

    robCtr.verifyBaseCase(baseTactic)
    robCtr.verifyUseCase(useTactic)
    robCtr.verifyStep(stepTactic)

    robCtr shouldBe 'verified

    Contract.save(robCtr, "pt3-robot.cbcps")
  }

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val obsCtr: Contract = Contract.load("pt3-obstacle-remote.cbcps")
    val robCtr: Contract = Contract.load("pt3-robot.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    //CPO
    obsCtr.cpo(robCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt3-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    obsCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt3-obstacle-remote-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    robCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt3-robot-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withMathematica { implicit tool =>
    val obsCtr: Contract = Contract.load("pt3-obstacle-remote.cbcps")
    val robCtr: Contract = Contract.load("pt3-robot.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](obsCtr.cpo(robCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt3-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val obsSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](obsCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt3-obstacle-remote-side-" + v).get
    }
    }.toSeq: _*)
    val robotSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](robCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt3-robot-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(obsCtr, robCtr, X, cpo, obsSc, robotSc)

    sysCtr shouldBe 'verified
    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic Robot Obstacle Avoidance"

  it should "prove System" in withMathematica { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\running\\3-robot\\Mono.kyx")))
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\3-robot\\Mono.kyx")))

    val invariant =
      s"""ep>0 & D>=0 & S>=0
         | & abs(dIn-dIn0)<=D
         | & abs(poIn-poIn0)<=S*$t
         | & (sr>0 -> poIn!=pr)
         | & 0<=so&so<=S
         | & abs(d-d0)<=D
         | & abs(po-po0)<=S*$t
         | & po=poIn & d=dIn""".stripMargin.asFormula

    println(invariant)

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  //Z3
  behavior of "Component-based Robot Obstacle Avoidance Z3"

  it should "prove Obstacle-Remote Component" in withZ3 { implicit tool =>
    val t = Globals.runT
    val obs = new Component("Obstacle-Remote-Z3", "d:=*;?abs(d-d0)<=D;so:=*;?(0<=so&so<=S);".asProgram, ODESystem("po'=so".asDifferentialProgram))
    val obsI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("d".asVariable) -> "abs(d-d0)<=D".asFormula, Seq("po".asVariable) -> s"abs(po-po0)<=S*$t".asFormula),
      mutable.LinkedHashMap(Seq("d".asVariable) -> Seq("d0".asVariable), Seq("po".asVariable) -> Seq("po0".asVariable)))
    val obsCtr = new DelayContract(obs, obsI, And(Globals.initTOld, "D>=0 & d=d0 & S>=0 & po=po0 & so=0".asFormula), True, s"D>=0 & S>=0 & 0<=so&so<=S & abs(d-d0)<=D & abs(po-po0)<=S*$t".asFormula)

    obsCtr.verifyBaseCase(baseTactic)
    obsCtr.verifyUseCase(useTactic)
    obsCtr.verifyStep(stepTactic)

    obsCtr shouldBe 'verified

    Contract.save(obsCtr, "pt3-obstacle-remote-Z3.cbcps")
  }

  it should "prove Robot Component" in withZ3 { implicit tool =>
    val t = Globals.runT
    val rob = new Component("Robot-Z3", "{?abs(poIn-pr)>dIn*ep+S*ep;sr:=dIn;} ++ {?abs(poIn-pr)<=dIn*ep+S*ep;sr:=0;}".asProgram, ODESystem("pr'=sr".asDifferentialProgram))
    val robI = new Interface(
      mutable.LinkedHashMap(Seq("dIn".asVariable) -> "abs(dIn-dIn0)<=D".asFormula, Seq("poIn".asVariable) -> s"abs(poIn-poIn0)<=S*$t".asFormula),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("dIn".asVariable) -> Seq("dIn0".asVariable), Seq("poIn".asVariable) -> Seq("poIn0".asVariable), Seq("pr".asVariable) -> Seq("pr0".asVariable)))
    val robCtr = new DelayContract(rob, robI,
      And(Globals.initTOld, "ep>0 & D>=0 & dIn=dIn0 & S>=0 & poIn=poIn0 & sr=0".asFormula),
      "sr>0 -> poIn!=pr".asFormula,
      s"ep>0 & D>=0 & S>=0 & abs(dIn-dIn0)<=D & abs(poIn-poIn0)<=S*$t & (sr>0 -> poIn!=pr)".asFormula)

    robCtr.verifyBaseCase(baseTactic)
    robCtr.verifyUseCase(useTactic)
    robCtr.verifyStep(stepTactic)

    robCtr shouldBe 'verified

    Contract.save(robCtr, "pt3-robot-Z3.cbcps")
  }

  it should "prove CPO and Sideconditions" in withZ3 { implicit tool =>
    val obsCtr: Contract = Contract.load("pt3-obstacle-remote-Z3.cbcps")
    val robCtr: Contract = Contract.load("pt3-robot-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    //CPO
    obsCtr.cpo(robCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt3-cpo-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    obsCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt3-obstacle-remote-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    robCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt3-robot-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withZ3 { implicit tool =>
    val obsCtr: Contract = Contract.load("pt3-obstacle-remote-Z3.cbcps")
    val robCtr: Contract = Contract.load("pt3-robot-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](obsCtr.cpo(robCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt3-cpo-Z3-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val obsSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](obsCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt3-obstacle-remote-side-Z3-" + v).get
    }
    }.toSeq: _*)
    val robotSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](robCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt3-robot-side-Z3-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(obsCtr, robCtr, X, cpo, obsSc, robotSc)

    sysCtr shouldBe 'verified
//    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic Robot Obstacle Avoidance Z3"

  it should "prove System" in withZ3 { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\running\\3-robot\\Mono.kyx")))
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\3-robot\\Mono.kyx")))

    val invariant =
      s"""ep>0 & D>=0 & S>=0
         | & abs(dIn-dIn0)<=D
         | & abs(poIn-poIn0)<=S*$t
         | & (sr>0 -> poIn!=pr)
         | & 0<=so&so<=S
         | & abs(d-d0)<=D
         | & abs(po-po0)<=S*$t
         | & po=poIn & d=dIn""".stripMargin.asFormula

    println(invariant)

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }


  /*===========================*
   * Case Study 1 - ETCS (pt4) *
   *===========================*/

  //Mathematica
  behavior of "Component-based ETCS"

  it should "prove RBC Component" in withMathematica { implicit tool =>
    val rbc = new Component("RBC",
      (
        """state := drive; m :=*; d :=*; vdes :=*; ?d >= 0 & d0^2 - d^2 <= 2*b*(m-m0) & vdes >= 0;
          |++ state := brake;"""
        ).stripMargin.asProgram,
      ODESystem("H'=0".asDifferentialProgram)
    )
    val rbcI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(
        Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable) -> ("(state=brake & m0=m & d0=d) | (state=drive & d >= 0 & d0^2 - d^2 <= 2*b*(m-m0) & vdes >= 0)").asFormula
      ),
      mutable.LinkedHashMap(Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable) -> Seq("state0".asVariable, "m0".asVariable, "d0".asVariable, "vdes0".asVariable))
    )
    val rbcCtr = new DelayContract(rbc, rbcI,
      ("""b>0
         | & drive=0
         | & brake=1
         | & state=drive
         | & vdes=0
         | & state0=state
         | & vdes0=vdes
         | & d0=d
         | & m0=m
         | & ep>0
         | & d>=0"""
        ).stripMargin.asFormula,
      True,
      """b>0
        | & drive=0
        | & brake=1
        | & ep>0
        |& ((
        |  state=brake
        |  & m0=m & d0=d
        |) | (
        |  state=drive
        |  & d >= 0
        |  & d0^2 - d^2 <= 2*b*(m-m0)
        |  & vdes >= 0
        |))""".stripMargin.asFormula)

    rbcCtr.verifyBaseCase(baseTactic)
    rbcCtr.verifyUseCase(useTactic)

    val rbcStepTactic = master()
    rbcCtr.verifyStep(rbcStepTactic)

    rbcCtr shouldBe 'verified

    Contract.save(rbcCtr, "pt4-rbc.cbcps")
  }

  it should "prove Train Component" in withMathematica { implicit tool =>
    val train = new Component("Train",
      """{
        |    ?v <= vdesIn; a:=*; ?-b <= a & a <= A;
        | ++ ?v >= vdesIn; a:=*; ?-b <= a & a <  0;
        |}
        |SB := (v^2 - dIn^2)/(2*b) + (A/b+1)*(A/2*ep^2+ep*v);
        |{
        |    ?  mIn-z<=SB | stateIn=brake; a := -b;
        | ++ ?!(mIn-z<=SB | stateIn=brake);
        |}""".stripMargin.asProgram,
      ODESystem(
        s"""z'=v,
           |v' = a""".stripMargin.asDifferentialProgram, s"v >= 0".asFormula)
    )
    val trainI = new Interface(
      mutable.LinkedHashMap(
        Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> ("(stateIn=brake & mIn0=mIn & dIn0=dIn) | (stateIn=drive & dIn >= 0 & dIn0^2 - dIn^2 <= 2*b*(mIn-mIn0) & vdesIn >= 0)").asFormula
      ),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("stateIn0".asVariable, "mIn0".asVariable, "dIn0".asVariable, "vdesIn0".asVariable))
    )
    val trainCtr = new DelayContract(train, trainI,
      """A>=0
        | & b>0
        | & drive=0
        | & brake=1
        | & stateIn=drive
        | & vdesIn=0
        | & dIn=0
        | & v=0
        | & z<=mIn
        | & dIn0=dIn
        | & mIn0=mIn
        | & stateIn0=stateIn
        | & vdesIn0=vdesIn
        | & ep>0""".stripMargin.asFormula,
      "z >= mIn -> v <= dIn".asFormula,
      """v^2 - dIn^2 <= 2*b*(mIn-z)
        |& dIn >= 0
        |& drive=0
        |& brake=1
        |& b>0
        |& ep>0
        |& A>=0""".stripMargin.asFormula)

    trainCtr.verifyBaseCase(baseTactic)
    trainCtr.verifyUseCase(useTactic)

    //--> NOPE @todo proves only when notL is disabled in normalize, because diffSolve hides facts
    val trainStepTactic = master() //implyR('R) & chase(1) & normalize(andR('R), skip, skip) & OnAll(diffSolve()('R)) & OnAll(normalize partial) & OnAll(speculativeQE)

    trainCtr.verifyStep(trainStepTactic)

    trainCtr shouldBe 'verified

    Contract.save(trainCtr, "pt4-train.cbcps")
  }

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val rbcCtr: Contract = Contract.load("pt4-rbc.cbcps")
    val trainCtr: Contract = Contract.load("pt4-train.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable)
    )

    //CPO
    rbcCtr.cpo(trainCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt4-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    rbcCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt4-rbc-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    trainCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt4-train-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withMathematica { implicit tool =>
    val rbcCtr: Contract = Contract.load("pt4-rbc.cbcps")
    val trainCtr: Contract = Contract.load("pt4-train.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](rbcCtr.cpo(trainCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt4-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val rbcSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](rbcCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt4-rbc-side-" + v).get
    }
    }.toSeq: _*)
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](trainCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt4-train-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(rbcCtr, trainCtr, X, cpo, rbcSc, trainSc)

    sysCtr shouldBe 'verified
    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic ETCS"

  it should "prove System" in withMathematica { implicit tool =>
    val t = Globals.t
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\casestudies\\1-etcs\\Mono.kyx")))
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\casestudies\\1-etcs\\sys-etcs.kyx")))

    val invariant =
      """b>0
        | & drive=0
        | & brake=1
        | & ep>0
        |& ((
        |  state=brake
        |  & m0=m & d0=d
        |) | (
        |  state=drive
        |  & d >= 0
        |  & d0^2 - d^2 <= 2*b*(m-m0)
        |  & vdes >= 0
        |))
        |& v^2 - dIn^2 <= 2*b*(mIn-z)
        |& dIn >= 0
        |& drive=0
        |& brake=1
        |& b>0
        |& ep>0
        |& A>=0
        |& d=dIn
        |& vdes=vdesIn
        |& state=stateIn
        |& m=mIn""".stripMargin.asFormula

    /*
& d0=d0In
& vdes0=vdes0In
& state0=state0In
& m0=m0In
     */

    println(invariant)

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  //Z3

  behavior of "Component-based ETCS Z3"

  it should "prove RBC Component" in withZ3 { implicit tool =>
    val rbc = new Component("RBC-Z3",
      (
        """state := drive; m :=*; d :=*; vdes :=*; ?d >= 0 & d0^2 - d^2 <= 2*b*(m-m0) & vdes >= 0;
          |++ state := brake;"""
        ).stripMargin.asProgram,
      ODESystem("H'=0".asDifferentialProgram)
    )
    val rbcI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(
        Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable) -> ("(state=brake & m0=m & d0=d) | (state=drive & d >= 0 & d0^2 - d^2 <= 2*b*(m-m0) & vdes >= 0)").asFormula
      ),
      mutable.LinkedHashMap(Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable) -> Seq("state0".asVariable, "m0".asVariable, "d0".asVariable, "vdes0".asVariable))
    )
    val rbcCtr = new DelayContract(rbc, rbcI,
      ("""b>0
         | & drive=0
         | & brake=1
         | & state=drive
         | & vdes=0
         | & state0=state
         | & vdes0=vdes
         | & d0=d
         | & m0=m
         | & ep>0
         | & d>=0"""
        ).stripMargin.asFormula,
      True,
      """b>0
        | & drive=0
        | & brake=1
        | & ep>0
        |& ((
        |  state=brake
        |  & m0=m & d0=d
        |) | (
        |  state=drive
        |  & d >= 0
        |  & d0^2 - d^2 <= 2*b*(m-m0)
        |  & vdes >= 0
        |))""".stripMargin.asFormula)

    rbcCtr.verifyBaseCase(baseTactic)
    rbcCtr.verifyUseCase(useTactic)

    val rbcStepTactic = master()
    rbcCtr.verifyStep(rbcStepTactic)

    rbcCtr shouldBe 'verified

    Contract.save(rbcCtr, "pt4-rbc-Z3.cbcps")
  }

  it should "prove Train Component" in withZ3 { implicit tool =>
    val train = new Component("Train-Z3",
      """{
        |    ?v <= vdesIn; a:=*; ?-b <= a & a <= A;
        | ++ ?v >= vdesIn; a:=*; ?-b <= a & a <  0;
        |}
        |SB := (v^2 - dIn^2)/(2*b) + (A/b+1)*(A/2*ep^2+ep*v);
        |{
        |    ?  mIn-z<=SB | stateIn=brake; a := -b;
        | ++ ?!(mIn-z<=SB | stateIn=brake);
        |}""".stripMargin.asProgram,
      ODESystem(
        s"""z'=v,
           |v' = a""".stripMargin.asDifferentialProgram, s"v >= 0".asFormula)
    )
    val trainI = new Interface(
      mutable.LinkedHashMap(
        Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> ("(stateIn=brake & mIn0=mIn & dIn0=dIn) | (stateIn=drive & dIn >= 0 & dIn0^2 - dIn^2 <= 2*b*(mIn-mIn0) & vdesIn >= 0)").asFormula
      ),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("stateIn0".asVariable, "mIn0".asVariable, "dIn0".asVariable, "vdesIn0".asVariable))
    )
    val trainCtr = new DelayContract(train, trainI,
      """A>=0
        | & b>0
        | & drive=0
        | & brake=1
        | & stateIn=drive
        | & vdesIn=0
        | & dIn=0
        | & v=0
        | & z<=mIn
        | & dIn0=dIn
        | & mIn0=mIn
        | & stateIn0=stateIn
        | & vdesIn0=vdesIn
        | & ep>0""".stripMargin.asFormula,
      "z >= mIn -> v <= dIn".asFormula,
      """v^2 - dIn^2 <= 2*b*(mIn-z)
        |& dIn >= 0
        |& drive=0
        |& brake=1
        |& b>0
        |& ep>0
        |& A>=0""".stripMargin.asFormula)

    trainCtr.verifyBaseCase(baseTactic)
    trainCtr.verifyUseCase(useTactic)

    //--> NOPE @todo proves only when notL is disabled in normalize, because diffSolve hides facts
    val trainStepTactic = master() //implyR('R) & chase(1) & normalize & OnAll(diffSolve('R)) & OnAll(QE)  //& normalize(andR('R), skip, skip) & OnAll(diffSolve('R)) & OnAll(normalize) & OnAll(speculativeQE) //master()

    trainCtr.verifyStep(trainStepTactic)

    trainCtr shouldBe 'verified

    Contract.save(trainCtr, "pt4-train-Z3.cbcps")
  }

  it should "prove CPO and Sideconditions" in withZ3 { implicit tool =>
    val rbcCtr: Contract = Contract.load("pt4-rbc-Z3.cbcps")
    val trainCtr: Contract = Contract.load("pt4-train-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable)
    )

    //CPO
    rbcCtr.cpo(trainCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt4-cpo-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    rbcCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt4-rbc-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    trainCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt4-train-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withZ3 { implicit tool =>
    val rbcCtr: Contract = Contract.load("pt4-rbc-Z3.cbcps")
    val trainCtr: Contract = Contract.load("pt4-train-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](rbcCtr.cpo(trainCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt4-cpo-Z3-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val rbcSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](rbcCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt4-rbc-side-Z3-" + v).get
    }
    }.toSeq: _*)
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](trainCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt4-train-side-Z3-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(rbcCtr, trainCtr, X, cpo, rbcSc, trainSc)

    sysCtr shouldBe 'verified
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic ETCS Z3"

  it should "prove System" in withZ3 { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\casestudies\\1-etcs\\sys-etcs.kyx")))
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\casestudies\\1-etcs\\Mono.kyx")))

    val invariant =
      """b>0
        | & drive=0
        | & brake=1
        | & ep>0
        |& ((
        |  state=brake
        |  & m0=m & d0=d
        |) | (
        |  state=drive
        |  & d >= 0
        |  & d0^2 - d^2 <= 2*b*(m-m0)
        |  & vdes >= 0
        |))
        |& v^2 - dIn^2 <= 2*b*(mIn-z)
        |& dIn >= 0
        |& drive=0
        |& brake=1
        |& b>0
        |& ep>0
        |& A>=0
        |& d=dIn
        |& vdes=vdesIn
        |& state=stateIn
        |& m=mIn""".stripMargin.asFormula

    /*
& d0=d0In
& vdes0=vdes0In
& state0=state0In
& m0=m0In
     */

    println(invariant)

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }


  /*============================*
   * Case Study 2 - Robix (pt5) *
   *============================*/

  //Mathematica

  behavior of "Component-based Robix"

  it should "prove Robot Component" in withMathematica { implicit tool =>
    val t = Globals.runT

    val rob = new Component("Robix-Robot",
      (
        """{ /* brake on current curve or remain stopped */
          | { a := -B; }
          | ++
          | { ?v = 0; a := 0; w := 0; }
          | ++
          | /* or choose a new safe curve */
          | { a :=*; ?-B <= a & a <= A;
          |   k :=*;
          |   w :=*; ?v * k = w;
          |
          | /* use that curve, if it is a safe one (admissible velocities) */
          | ? abs(x-xoIn) > v^2/(2*B) + V*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V))
          |              | abs(y-yoIn) > v^2/(2*B) + V*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V));
          | }
          |}"""
        ).stripMargin.asProgram,
      ODESystem(
        (
          """x' = v * dx,
            |y' = v * dy,
            |dx' = -w * dy,
            |dy' = w * dx,
            |v' = a,
            |w' = a*k""").stripMargin.asDifferentialProgram,
        "t <= ep & v >= 0".asFormula)
    )
    val robI = new Interface(
      mutable.LinkedHashMap(
        Seq("xoIn".asVariable) -> ("-V*" + t + " <= xoIn-xoIn0 & xoIn-xoIn0 <= V*" + t).asFormula,
        Seq("yoIn".asVariable) -> ("-V*" + t + " <= yoIn-yoIn0 & yoIn-yoIn0 <= V*" + t).asFormula
      ),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("xoIn".asVariable) -> Seq("xoIn0".asVariable), Seq("yoIn".asVariable) -> Seq("yoIn0".asVariable))
    )
    val robCtr = new DelayContract(rob, robI,
      (
        """ v >= 0
          | & ( abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
          |               | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))
          | & dx^2 + dy^2 = 1
          | & A >= 0
          | & B > 0
          | & V >= 0
          | & ep > 0
          | & xoIn0 = xoIn
          | & yoIn0 = yoIn
          | & t=tOld"""
        ).stripMargin.asFormula,
      "(v > 0 -> (x - xoIn)^2 + (y - yoIn)^2 > 0)".asFormula,
      s"""v >= 0
         | & A >= 0
         | & B > 0
         | & V >= 0
         | & ep > 0
         | & dx^2+dy^2 = 1
         | & 0 <= $t & $t <= ep
         | & -V*($t) <= xoIn-xoIn0 & xoIn-xoIn0 <= V*($t) & -V*($t) <= yoIn-yoIn0 & yoIn-yoIn0 <= V*($t)
         | & (v = 0 | abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
         |          | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula
    )

    robCtr.verifyBaseCase(baseTactic)
    robCtr.verifyUseCase(useTactic)

    def di1(a: String, t: String): DependentPositionTactic = diffInvariant(
      s"0<=$t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*($t)".asFormula,
      s"-($t) * (v - $a/2*($t)) <= x - old(x) & x - old(x) <= ($t) * (v - $a/2*($t))".asFormula,
      s"-($t) * (v - $a/2*($t)) <= y - old(y) & y - old(y) <= ($t) * (v - $a/2*($t))".asFormula)

    val dw1: BelleExpr = exhaustiveEqR2L(hide = true)('Llast) * 3 /* 3 old(...) in DI */ & (andL('_) *) &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    def accArithTactic1: BelleExpr = (alphaRule *) & printIndexed("Before replaceTransform") &
      replaceTransform("ep".asTerm, "(t-tOld)".asTerm)(-9) & print("After replaceTransform") &
      speculativeQE & print("Proved acc arithmetic")

    val robStepTactic = print("Induction step") & implyR('R) & (andL('L) *) & chase(1) & print("After chase") & normalize(andR('R), skip, skip) & printIndexed("After normalize") < (
      print("Braking branch") & di1("-B", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize(choiceb('R) | composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) & print("After braking normalize") & OnAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di1("0", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize(choiceb('R) | composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) & OnAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di1("a", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize(betaRule, skip, skip) & print("After acc normalize") & OnAll(hideFactsAbout("dx", "dy", "k", "k_0") partial) < (
        hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic1,
        hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic1
      ) & print("Acceleration branch done")
    ) & print("Induction step done")
    robCtr.verifyStep(robStepTactic)

    robCtr shouldBe 'verified

    Contract.save(robCtr, "pt5-robot.cbcps")
  }

  it should "prove Obstacle Component" in withMathematica { implicit tool =>
    val t = Globals.runT

    val obs = new Component("Robix-Obstacle",
      """dxo :=*;
        |dyo :=*;
        |?dxo^2 + dyo^2 <= V^2;""".stripMargin.asProgram,
      ODESystem(
        """xo' = dxo,
          |yo' = dyo""".stripMargin.asDifferentialProgram)
    )
    val obsI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(
        Seq("xo".asVariable) -> s"-V*$t <= xo-xo0 & xo-xo0 <= V*$t".asFormula,
        Seq("yo".asVariable) -> s"-V*$t <= yo-yo0 & yo-yo0 <= V*$t".asFormula
      ),
      mutable.LinkedHashMap(
        Seq("xo".asVariable) -> Seq("xo0".asVariable),
        Seq("yo".asVariable) -> Seq("yo0".asVariable)
      )
    )
    val obsCtr = new DelayContract(obs, obsI,
      """ep > 0
        |& t = tOld
        |& V >= 0
        |& xo = xo0
        |& yo = yo0""".stripMargin.asFormula,
      "true".asFormula,
      s"""V >= 0
         |& 0 <= $t
         |& $t <= ep
         |& -V*$t <= xo-xo0
         |& xo-xo0 <= V*$t
         |& -V*$t <= yo-yo0
         |& yo-yo0 <= V*$t""".stripMargin.asFormula
    )


    obsCtr.verifyBaseCase(baseTactic)
    obsCtr.verifyUseCase(useTactic)

    val obsStepTactic = master()
    obsCtr.verifyStep(obsStepTactic)

    obsCtr shouldBe 'verified

    Contract.save(obsCtr, "pt5-obstacle.cbcps")
  }

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val robCtr: Contract = Contract.load("pt5-robot.cbcps")
    val obsCtr: Contract = Contract.load("pt5-obstacle.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xoIn".asVariable) -> Seq("xo".asVariable),
      Seq("yoIn".asVariable) -> Seq("yo".asVariable)
    )
    //CPO
    robCtr.cpo(obsCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt5-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    robCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt5-robot-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    obsCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt5-obstacle-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  // hack because of KeYmaeraX limitations
  it should "prove Composition" in withMathematica { implicit tool =>
    val robCtr: Contract = Contract.load("pt5-robot.cbcps")
    val obsCtr: Contract = Contract.load("pt5-obstacle.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xoIn".asVariable) -> Seq("xo".asVariable),
      Seq("yoIn".asVariable) -> Seq("yo".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](robCtr.cpo(obsCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt5-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val rbcSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](robCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt5-robot-side-" + v).get
    }
    }.toSeq: _*)
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](obsCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt5-obstacle-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    Contract.hack = 1
    val verify = true
    val sysCtr: Contract = Contract.composeWithLemmas(robCtr, obsCtr, X, cpo, rbcSc, trainSc, verify)
    Contract.hack = 0

    if (verify)
      sysCtr shouldBe 'verified
    println("CTR: " + sysCtr.isVerified())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic Robix"

  //Tactic missing!
  ignore should "prove System" in withMathematica { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\casestudies\\2-robix\\sys-robix.kyx")))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & xo = xor & yo = yor
        | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V*(v/B)
        |          | abs(y-yo) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "0<=t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V <= xo - old(xo) & xo - old(xo) <= t * V".asFormula,
      "-t * V <= yo - old(yo) & yo - old(yo) <= t * V".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide = true)('Llast) * 5 /* 5 old(...) in DI */ & (andL('_) *) &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule *) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_) *) & loop(invariant)('R) < (
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & printIndexed("After normalize") < (
      print("Braking branch 1") & di("-B")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Braking branch 1 done"),
      print("Braking branch 2") & di("-B")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Braking branch 2 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 1 done"),
      print("Acceleration branch 1") & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) < (
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
      ) & print("Acceleration branch 1 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 2 done"),
      print("Acceleration branch 2") & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) < (
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
      ) & print("Acceleration branch 2 done")
    ) & print("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }


  //Z3
  behavior of "Component-based Robix Z3"

  it should "prove Robot Component" in withZ3 { implicit tool =>
    val t = Globals.runT

    val rob = new Component("Robix-Robot-Z3",
      (
        """{ /* brake on current curve or remain stopped */
          | { a := -B; }
          | ++
          | { ?v = 0; a := 0; w := 0; }
          | ++
          | /* or choose a new safe curve */
          | { a :=*; ?-B <= a & a <= A;
          |   k :=*;
          |   w :=*; ?v * k = w;
          |
          | /* use that curve, if it is a safe one (admissible velocities) */
          | ? abs(x-xoIn) > v^2/(2*B) + V*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V))
          |              | abs(y-yoIn) > v^2/(2*B) + V*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V));
          | }
          |}"""
        ).stripMargin.asProgram,
      ODESystem(
        (
          """x' = v * dx,
            |y' = v * dy,
            |dx' = -w * dy,
            |dy' = w * dx,
            |v' = a,
            |w' = a*k""").stripMargin.asDifferentialProgram,
        "t <= ep & v >= 0".asFormula)
    )
    val robI = new Interface(
      mutable.LinkedHashMap(
        Seq("xoIn".asVariable) -> ("-V*" + t + " <= xoIn-xoIn0 & xoIn-xoIn0 <= V*" + t).asFormula,
        Seq("yoIn".asVariable) -> ("-V*" + t + " <= yoIn-yoIn0 & yoIn-yoIn0 <= V*" + t).asFormula
      ),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("xoIn".asVariable) -> Seq("xoIn0".asVariable), Seq("yoIn".asVariable) -> Seq("yoIn0".asVariable))
    )
    val robCtr = new DelayContract(rob, robI,
      (
        """ v >= 0
          | & ( abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
          |               | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))
          | & dx^2 + dy^2 = 1
          | & A >= 0
          | & B > 0
          | & V >= 0
          | & ep > 0
          | & xoIn0 = xoIn
          | & yoIn0 = yoIn
          | & t=tOld"""
        ).stripMargin.asFormula,
      "(v > 0 -> (x - xoIn)^2 + (y - yoIn)^2 > 0)".asFormula,
      s"""v >= 0
         | & A >= 0
         | & B > 0
         | & V >= 0
         | & ep > 0
         | & dx^2+dy^2 = 1
         | & 0 <= $t & $t <= ep
         | & -V*($t) <= xoIn-xoIn0 & xoIn-xoIn0 <= V*($t) & -V*($t) <= yoIn-yoIn0 & yoIn-yoIn0 <= V*($t)
         | & (v = 0 | abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
         |          | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula
    )

    robCtr.verifyBaseCase(baseTactic)
    robCtr.verifyUseCase(useTactic)

    def di1(a: String, t: String): DependentPositionTactic = diffInvariant(
      s"0<=$t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*($t)".asFormula,
      s"-($t) * (v - $a/2*($t)) <= x - old(x) & x - old(x) <= ($t) * (v - $a/2*($t))".asFormula,
      s"-($t) * (v - $a/2*($t)) <= y - old(y) & y - old(y) <= ($t) * (v - $a/2*($t))".asFormula)

    val dw1: BelleExpr = exhaustiveEqR2L(hide = true)('Llast) * 3 /* 3 old(...) in DI */ & (andL('_) *) &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    def accArithTactic1: BelleExpr = (alphaRule *) & printIndexed("Before replaceTransform") &
      replaceTransform("ep".asTerm, "(t-tOld)".asTerm)(-9) & print("After replaceTransform") &
      speculativeQE & print("Proved acc arithmetic")

    val robStepTactic = print("Induction step") & implyR('R) & (andL('L) *) & chase(1) & print("After chase") & normalize(andR('R), skip, skip) & printIndexed("After normalize") < (
      print("Braking branch") & di1("-B", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize(choiceb('R) | composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) & print("After braking normalize") & OnAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di1("0", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize(choiceb('R) | composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) & OnAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di1("a", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize(betaRule, skip, skip) & print("After acc normalize") & OnAll(hideFactsAbout("dx", "dy", "k", "k_0") partial) < (
        hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic1,
        hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic1
      ) & print("Acceleration branch done")
    ) & print("Induction step done")
    robCtr.verifyStep(robStepTactic)

    robCtr shouldBe 'verified

    Contract.save(robCtr, "pt5-robot-Z3.cbcps")
  }

  it should "prove Obstacle Component" in withZ3 { implicit tool =>
    val t = Globals.runT

    val obs = new Component("Robix-Obstacle-Z3",
      """dxo :=*;
        |dyo :=*;
        |?dxo^2 + dyo^2 <= V^2;""".stripMargin.asProgram,
      ODESystem(
        """xo' = dxo,
          |yo' = dyo""".stripMargin.asDifferentialProgram)
    )
    val obsI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(
        Seq("xo".asVariable) -> s"-V*$t <= xo-xo0 & xo-xo0 <= V*$t".asFormula,
        Seq("yo".asVariable) -> s"-V*$t <= yo-yo0 & yo-yo0 <= V*$t".asFormula
      ),
      mutable.LinkedHashMap(
        Seq("xo".asVariable) -> Seq("xo0".asVariable),
        Seq("yo".asVariable) -> Seq("yo0".asVariable)
      )
    )
    val obsCtr = new DelayContract(obs, obsI,
      """ep > 0
        |& t = tOld
        |& V >= 0
        |& xo = xo0
        |& yo = yo0""".stripMargin.asFormula,
      "true".asFormula,
      s"""V >= 0
         |& 0 <= $t
         |& $t <= ep
         |& -V*$t <= xo-xo0
         |& xo-xo0 <= V*$t
         |& -V*$t <= yo-yo0
         |& yo-yo0 <= V*$t""".stripMargin.asFormula
    )


    obsCtr.verifyBaseCase(baseTactic)
    obsCtr.verifyUseCase(useTactic)

    val obsStepTactic = master()


    obsCtr.verifyStep(obsStepTactic)

    obsCtr shouldBe 'verified

    Contract.save(obsCtr, "pt5-obstacle-Z3.cbcps")
  }

  it should "prove CPO and Sideconditions" in withZ3 { implicit tool =>
    val robCtr: Contract = Contract.load("pt5-robot-Z3.cbcps")
    val obsCtr: Contract = Contract.load("pt5-obstacle-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xoIn".asVariable) -> Seq("xo".asVariable),
      Seq("yoIn".asVariable) -> Seq("yo".asVariable)
    )
    //CPO
    robCtr.cpo(obsCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt5-cpo-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    robCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt5-robot-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    obsCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt5-obstacle-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  // hack because of KeYmaeraX limitations
  it should "prove Composition" in withZ3 { implicit tool =>
    val robCtr: Contract = Contract.load("pt5-robot-Z3.cbcps")
    val obsCtr: Contract = Contract.load("pt5-obstacle-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xoIn".asVariable) -> Seq("xo".asVariable),
      Seq("yoIn".asVariable) -> Seq("yo".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](robCtr.cpo(obsCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt5-cpo-Z3-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val rbcSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](robCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt5-robot-side-Z3-" + v).get
    }
    }.toSeq: _*)
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](obsCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt5-obstacle-side-Z3-" + v).get
    }
    }.toSeq: _*)

    //Compose
    Contract.hack = 1
    val verify = false
    val sysCtr: Contract = Contract.composeWithLemmas(robCtr, obsCtr, X, cpo, rbcSc, trainSc, verify)
    Contract.hack = 0

    if (verify)
      sysCtr shouldBe 'verified
    //    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic Robix Z3"

  //Tactic missing!
  ignore should "prove System" in withZ3 { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\casestudies\\2-robix\\sys-robix.kyx")))
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\casestudies\\2-robix\\Mono.kyx")))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & xo = xor & yo = yor
        | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V*(v/B)
        |          | abs(y-yo) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "0<=t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V <= xo - old(xo) & xo - old(xo) <= t * V".asFormula,
      "-t * V <= yo - old(yo) & yo - old(yo) <= t * V".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide = true)('Llast) * 5 /* 5 old(...) in DI */ & (andL('_) *) &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule *) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_) *) & loop(invariant)('R) < (
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & printIndexed("After normalize") < (
      print("Braking branch 1") & di("-B")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Braking branch 1 done"),
      print("Braking branch 2") & di("-B")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Braking branch 2 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 1 done"),
      print("Acceleration branch 1") & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) < (
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
      ) & print("Acceleration branch 1 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 2 done"),
      print("Acceleration branch 2") & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) < (
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
      ) & print("Acceleration branch 2 done")
    ) & print("Induction step done")
    ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  /*=========================================*
   * Case Study 3 - Local Lane Control (pt6) *
   *=========================================*/

  //Mathematica
  behavior of "Component-based LLC"

  it should "prove Leader Component" in withMathematica { implicit tool =>
    val t = Globals.runT

    val lead = new Component("Leader",
      "al :=*; ?-B <= al & al <= A;".asProgram,
      ODESystem("xl' = vl, vl' = al".asDifferentialProgram, "vl >= 0".asFormula)
    )
    val leadI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(
        Seq("xl".asVariable, "vl".asVariable) -> (s"0 <= vl & -B*$t <= vl-vl0 & vl-vl0 <= A*$t & xl-xl0 >= (vl+vl0)/2*$t").asFormula
      ),
      mutable.LinkedHashMap(Seq("xl".asVariable, "vl".asVariable) -> Seq("xl0".asVariable, "vl0".asVariable))
    )
    val leadCtr = new DelayContract(lead, leadI,
      ("""ep > 0
         | & A >= 0
         | & B > 0
         | & xl = xl0
         | & vl = vl0
         | & 0 <= vl
         | & t=tOld"""
        ).stripMargin.asFormula,
      True,
      s"""ep > 0
         | & A >= 0
         | & B > 0
         | & 0 <= $t & $t <= ep
         | & xl-xl0 >= (vl+vl0)/2*$t
         | & 0 <= vl
         | & -B*$t <= vl-vl0
         | & vl-vl0 <= A*$t""".stripMargin.asFormula)

    leadCtr.verifyBaseCase(baseTactic)
    leadCtr.verifyUseCase(useTactic)

    val leadStepTactic = master()
    leadCtr.verifyStep(leadStepTactic)

    leadCtr shouldBe 'verified

    Contract.save(leadCtr, "pt6-leader.cbcps")
  }

  it should "prove Follower Component" in withMathematica { implicit tool =>
    val t = Globals.runT

    val follow = new Component("Follower",
      """{
        | af := -B;
        |  ++ ?vf=0; af:=0;
        |  ++ ?xf + vf^2/(2*B) + (A/B+1)*(A/2*ep^2 + ep*vf) < xlIn + vlIn^2/(2*B); af :=*; ?-B <= af & af <= A;
        | }""".stripMargin.asProgram,
      ODESystem(
        "xf' = vf,vf' = af".asDifferentialProgram, s"vf >= 0".asFormula)
    )
    val followI = new Interface(
      mutable.LinkedHashMap(
        Seq("xlIn".asVariable, "vlIn".asVariable) -> (s"0 <= vlIn & -B*$t <= vlIn-vlIn0 & vlIn-vlIn0 <= A*$t & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t").asFormula
      ),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xlIn0".asVariable, "vlIn0".asVariable))
    )
    val followCtr = new DelayContract(follow, followI,
      """ep > 0
        | & A >= 0
        | & B > 0
        | & t = 0
        | & vf >= 0
        | & xf < xlIn & xf + vf^2/(2*B) < xlIn + vlIn^2/(2*B)
        | & xlIn = xlIn0
        | & vlIn = vlIn0
        | & t = tOld
        | & 0 <= vlIn""".stripMargin.asFormula,
      "xf < xlIn".asFormula,
      s"""ep > 0
         | & A >= 0
         | & B > 0
         | & 0<= vf & xf < xlIn
         | & xf+vf^2/(2*B) < xlIn + vlIn^2/(2*B)
         | & 0 <= $t & $t <= ep
         | & 0 <= vlIn
         | & -B*$t <= vlIn-vlIn0
         | & vlIn-vlIn0 <= A*$t
         | & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t""".stripMargin.asFormula)

    followCtr.verifyBaseCase(baseTactic)
    followCtr.verifyUseCase(useTactic)

    val followStepTactic = implyR('R) & chase(1) & normalize(andR('R), skip, skip) &
      OnAll(diffSolve(1) partial) < (
        normalize & OnAll(speculativeQE),
        normalize & OnAll(speculativeQE),
        (normalize(betaRule, skip, skip) < (
          QE,
          allL("s_".asVariable, "t_".asVariable)(-20) & implyL(-20) < (hide(1) & QE, skip) & andL(-20)
            & exhaustiveEqL2R(true)(-18) & exhaustiveEqL2R(true)(-14) & exhaustiveEqL2R(true)(-13)
            & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE) & exhaustiveEqL2R(true)(-23)
            & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE)
            & hide(-13) & hide(-12) & hide(-6) & QE,
          exhaustiveEqL2R(true)(-18) & exhaustiveEqL2R(true)(-14) & exhaustiveEqL2R(true)(-13)
            & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE) & exhaustiveEqL2R(true)(-22)
            & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE)
            & allL("s_".asVariable, "t_".asVariable)(-17) & implyL(-17) < (hide(1) & QE, skip) & andL(-17)
            & hide(-13) & hide(-12) & hide(-6)
            & QE,
          QE,
          QE
        )
          )
      )

    followCtr.verifyStep(followStepTactic)

    followCtr shouldBe 'verified

    Contract.save(followCtr, "pt6-follower.cbcps")
  }

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val leadCtr: Contract = Contract.load("pt6-leader.cbcps")
    val followCtr: Contract = Contract.load("pt6-follower.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xl".asVariable, "vl".asVariable)
    )

    //CPO
    leadCtr.cpo(followCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt6-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    leadCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt6-leader-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    followCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt6-follower-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withMathematica { implicit tool =>
    val leadCtr: Contract = Contract.load("pt6-leader.cbcps")
    val followCtr: Contract = Contract.load("pt6-follower.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xl".asVariable, "vl".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](leadCtr.cpo(followCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt6-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val rbcSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](leadCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt6-leader-side-" + v).get
    }
    }.toSeq: _*)
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](followCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt6-follower-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(leadCtr, followCtr, X, cpo, rbcSc, trainSc)

    sysCtr shouldBe 'verified
    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic LLC"

  it should "prove System" in withMathematica { implicit tool =>
    val t = Globals.runT
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\casestudies\\3-llc\\sys-llcs.kyx")))
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\casestudies\\3-llc\\system.kyx")))

    val invariant =
      s"""ep > 0
         | & A >= 0
         | & B > 0
         | & 0<= vf & xf < xlIn
         | & xf+vf^2/(2*B) < xlIn + vlIn^2/(2*B)
         | & 0 <= $t & $t <= ep
         | & 0 <= vlIn
         | & -B*$t <= vlIn-vlIn0
         | & vlIn-vlIn0 <= A*$t
         | & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t
         | & xl-xl0 >= (vl+vl0)/2*$t
         | & 0 <= vl
         | & vlIn=vl
         | & xlIn=xl
         | & vlIn0=vl0
         | & xlIn0=xl0""".stripMargin.asFormula


    println(invariant)

    //    val sysStepTactic = chase(1) & normalize & print("here") & //(andR('R), skip, skip) &
    //      OnAll(diffSolve(1) partial) & print("branches...") < (
    //      normalize & OnAll(speculativeQE) & print("brake1"),
    //      normalize & OnAll(speculativeQE) & print("brake2"),
    //      normalize & OnAll(speculativeQE) & print("stop1"),
    //      print("acc1"),
    //      normalize & OnAll(speculativeQE) & print("stop2"),
    //      print("acc2")
    //      //      normalize(betaRule, skip, skip) & print("branches...")
    //    )
    //
    //    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
    //      skip, //print("Base case") & baseTactic & print("Base case done"),
    //      skip, //print("Use case") & useTactic & print("Use case done"),
    //      print("Induction step") & sysStepTactic & printIndexed("Induction step done")
    //    ) & print("Proof done")


    val tactic = unfoldProgramNormalize & loop(invariant)(1) < (
      QE,
      QE,
      unfoldProgramNormalize & print("HERE1") < (
        diffSolve(1) & QE,
        diffSolve(1) & QE,
        diffSolve(1) & allR(1) & implyR(1) & implyR(1) & allL("t_".asTerm)(-24) & implyL(-24) & print("HERE2") < (
          hideR(1) & QE,
          hideL(-6) & transform("xf+vf^2/(2*B)+(A/B+1)*(A/2*t_^2+t_*vf) < xlr+vlr^2/(2*B)".asFormula)(-14) & andL(-23) & andL(-24) & andR(1) < (
            QE,
            andR(1) & print("HERE3") < (
              hideL(-1) & hideL(-6) & hideL(-23) & hideL(-19) & hideL(-16) & hideL(-13) & QE,
              andR(1) < (
                hideL(-1) & hideL(-6) & hideL(-23) & hideL(-9) & hideL(-12) & hideL(-14) & hideL(-16) & hideL(-1) & QE,
                hideL(-14) & QE
              )
            )
          )
        )
      )
    )

    proveBy(s, tactic) shouldBe 'proved
  }

  //Z3
  behavior of "Component-based LLC"

  it should "prove Leader Component" in withZ3 { implicit tool =>
    val t = Globals.runT

    val lead = new Component("Leader-Z3",
      "al :=*; ?-B <= al & al <= A;".asProgram,
      ODESystem("xl' = vl, vl' = al".asDifferentialProgram, "vl >= 0".asFormula)
    )
    val leadI = new Interface(
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(
        Seq("xl".asVariable, "vl".asVariable) -> (s"0 <= vl & -B*$t <= vl-vl0 & vl-vl0 <= A*$t & xl-xl0 >= (vl+vl0)/2*$t").asFormula
      ),
      mutable.LinkedHashMap(Seq("xl".asVariable, "vl".asVariable) -> Seq("xl0".asVariable, "vl0".asVariable))
    )
    val leadCtr = new DelayContract(lead, leadI,
      ("""ep > 0
         | & A >= 0
         | & B > 0
         | & xl = xl0
         | & vl = vl0
         | & 0 <= vl
         | & t=tOld"""
        ).stripMargin.asFormula,
      True,
      s"""ep > 0
         | & A >= 0
         | & B > 0
         | & 0 <= $t & $t <= ep
         | & xl-xl0 >= (vl+vl0)/2*$t
         | & 0 <= vl
         | & -B*$t <= vl-vl0
         | & vl-vl0 <= A*$t""".stripMargin.asFormula)

    leadCtr.verifyBaseCase(baseTactic)
    leadCtr.verifyUseCase(useTactic)

    val leadStepTactic = master()
    leadCtr.verifyStep(leadStepTactic)

    leadCtr shouldBe 'verified

    Contract.save(leadCtr, "pt6-leader-Z3.cbcps")
  }

  it should "prove Follower Component" in withZ3 { implicit tool =>
    val t = Globals.runT

    val follow = new Component("Follower-Z3",
      """{
        | af := -B;
        |  ++ ?vf=0; af:=0;
        |  ++ ?xf + vf^2/(2*B) + (A/B+1)*(A/2*ep^2 + ep*vf) < xlIn + vlIn^2/(2*B); af :=*; ?-B <= af & af <= A;
        | }""".stripMargin.asProgram,
      ODESystem(
        "xf' = vf,vf' = af".asDifferentialProgram, s"vf >= 0".asFormula)
    )
    val followI = new Interface(
      mutable.LinkedHashMap(
        Seq("xlIn".asVariable, "vlIn".asVariable) -> (s"0 <= vlIn & -B*$t <= vlIn-vlIn0 & vlIn-vlIn0 <= A*$t & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t").asFormula
      ),
      mutable.LinkedHashMap.empty,
      mutable.LinkedHashMap(Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xlIn0".asVariable, "vlIn0".asVariable))
    )
    val followCtr = new DelayContract(follow, followI,
      """ep > 0
        | & A >= 0
        | & B > 0
        | & t = 0
        | & vf >= 0
        | & xf < xlIn & xf + vf^2/(2*B) < xlIn + vlIn^2/(2*B)
        | & xlIn = xlIn0
        | & vlIn = vlIn0
        | & t = tOld
        | & 0 <= vlIn""".stripMargin.asFormula,
      "xf < xlIn".asFormula,
      s"""ep > 0
         | & A >= 0
         | & B > 0
         | & 0<= vf & xf < xlIn
         | & xf+vf^2/(2*B) < xlIn + vlIn^2/(2*B)
         | & 0 <= $t & $t <= ep
         | & 0 <= vlIn
         | & -B*$t <= vlIn-vlIn0
         | & vlIn-vlIn0 <= A*$t
         | & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t""".stripMargin.asFormula)

    followCtr.verifyBaseCase(baseTactic)
    followCtr.verifyUseCase(useTactic)

    val followStepTactic = implyR('R) & chase(1) & normalize(andR('R), skip, skip) &
      OnAll(diffSolve(1) partial) < (
        normalize & OnAll(speculativeQE),
        normalize & OnAll(speculativeQE),
        (normalize(betaRule, skip, skip) < (
          QE,
          allL("s_".asVariable, "t_".asVariable)(-20) & implyL(-20) < (hide(1) & QE, skip) & andL(-20)
            & exhaustiveEqL2R(true)(-18) & exhaustiveEqL2R(true)(-14) & exhaustiveEqL2R(true)(-13)
            & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE) & exhaustiveEqL2R(true)(-23)
            & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE)
            & hide(-13) & hide(-12) & hide(-6) & QE,
          exhaustiveEqL2R(true)(-18) & exhaustiveEqL2R(true)(-14) & exhaustiveEqL2R(true)(-13)
            & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE) & exhaustiveEqL2R(true)(-22)
            & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE)
            & allL("s_".asVariable, "t_".asVariable)(-17) & implyL(-17) < (hide(1) & QE, skip) & andL(-17)
            & hide(-13) & hide(-12) & hide(-6)
            & QE,
          QE,
          QE
        )
          )
      )

    followCtr.verifyStep(followStepTactic)

    followCtr shouldBe 'verified

    Contract.save(followCtr, "pt6-follower-Z3.cbcps")
  }

  it should "prove CPO and Sideconditions" in withZ3 { implicit tool =>
    val leadCtr: Contract = Contract.load("pt6-leader-Z3.cbcps")
    val followCtr: Contract = Contract.load("pt6-follower-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xl".asVariable, "vl".asVariable)
    )

    //CPO
    leadCtr.cpo(followCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt6-cpo-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    leadCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt6-leader-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    followCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt6-follower-side-Z3-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withZ3 { implicit tool =>
    val leadCtr: Contract = Contract.load("pt6-leader-Z3.cbcps")
    val followCtr: Contract = Contract.load("pt6-follower-Z3.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xl".asVariable, "vl".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](leadCtr.cpo(followCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt6-cpo-Z3-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val rbcSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](leadCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt6-leader-side-Z3-" + v).get
    }
    }.toSeq: _*)
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](followCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt6-follower-side-Z3-" + v).get
    }
    }.toSeq: _*)

    //      println("llc: "+Contract.composeWithLemmas(leadCtr, followCtr, X, cpo, rbcSc, trainSc).contract())

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(leadCtr, followCtr, X, cpo, rbcSc, trainSc)

    sysCtr shouldBe 'verified
    //      println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  behavior of "Monolithic LLC"

  it should "prove System" in withZ3 { implicit tool =>
    val t = Globals.runT
    val s = parseToSequent(new FileInputStream(new File("W:\\Users\\Andreas\\Documents\\Arbeit\\JKU\\svn-vde\\documents\\diss-am\\models\\casestudies\\3-llc\\sys-llc.kyx")))
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\casestudies\\3-llc\\system.kyx")))

    val invariant =
      s"""ep > 0
         | & A >= 0
         | & B > 0
         | & 0<= vf & xf < xlIn
         | & xf+vf^2/(2*B) < xlIn + vlIn^2/(2*B)
         | & 0 <= $t & $t <= ep
         | & 0 <= vlIn
         | & -B*$t <= vlIn-vlIn0
         | & vlIn-vlIn0 <= A*$t
         | & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t
         | & xl-xl0 >= (vl+vl0)/2*$t
         | & 0 <= vl
         | & vlIn=vl
         | & xlIn=xl
         | & vlIn0=vl0
         | & xlIn0=xl0""".stripMargin.asFormula


    println(invariant)

    //    val sysStepTactic = chase(1) & normalize & print("here") & //(andR('R), skip, skip) &
    //      OnAll(diffSolve(1) partial) & print("branches...") < (
    //      normalize & OnAll(speculativeQE) & print("brake1"),
    //      normalize & OnAll(speculativeQE) & print("brake2"),
    //      normalize & OnAll(speculativeQE) & print("stop1"),
    //      print("acc1"),
    //      normalize & OnAll(speculativeQE) & print("stop2"),
    //      print("acc2")
    //      //      normalize(betaRule, skip, skip) & print("branches...")
    //    )
    //
    //    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
    //      skip, //print("Base case") & baseTactic & print("Base case done"),
    //      skip, //print("Use case") & useTactic & print("Use case done"),
    //      print("Induction step") & sysStepTactic & printIndexed("Induction step done")
    //    ) & print("Proof done")

    val tactic = chase(1) & loop(invariant)(1) < (
      QE & print("1"),
      QE & print("2"),
      chase(1) & normalize & print("3") < (
        diffSolve(1) & QE,
        diffSolve(1) & QE,
        diffSolve(1) & QE,
        diffSolve(1) & QE,
        diffSolve(1) & QE,
        diffSolve(1) & allR(1) & implyR(1) & implyR(1) & allL("t_".asTerm)(-24) & implyL(-24) < (
          hideR(1) & QE,
          hideL(-6) & printIndexed("rt")
          //            & replaceTransform("xf+vf^2/(2*B)+(A/B+1)*(A/2*t_^2+t_*vf) < xlr+vlr^2/(2*B)".asFormula,-14) & andL(-23) & andL(-24) & andR(1)  <(
          //            QE,
          //            andR(1) & <(
          //              hideL(-1) & hideL(-6) & hideL(-23) & hideL(-19) & hideL(-16) & hideL(-13) & QE,
          //              andR(1) & <(
          //                hideL(-1) & hideL(-6) & hideL(-23) & hideL(-9) & hideL(-12) & hideL(-14) & hideL(-16) & hideL(-1) & QE,
          //                hideL(-14) & QE
          //              )
        )
      )
    )

    proveBy(s, tactic) shouldBe 'proved
  }

}

