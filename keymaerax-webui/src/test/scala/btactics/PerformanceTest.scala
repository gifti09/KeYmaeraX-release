package btactics

import java.io.{File, FileInputStream}

import cbcps._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentPositionTactic, Find, OnAll}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
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

  def stepTactic: BelleExpr = chase(1) & normalize & master()

  def sideTactic: BelleExpr = master()

  /*=====================================*
   * Running Example 1 - Traffic Control *
   *=====================================*/
  "Component-based Traffic Networks" should "prove Merge Component" in withMathematica { implicit tool =>
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


  it should "prove Split Component" in withMathematica { implicit tool =>
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

  it should "prove Traffic Light Component" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\1-traffic\\trafficlight.kyx")))

    val invariant =
      """tc<=Tc & go*(go-1) = 0 & t>=0 & tc>=0
        | & Tc>0 & T>0 & 0<=MAXIN & 0<=MAXOUT
        |	& l <= t * (2*in-out)/2+Tc*(out/2)
        |	& l + (Tc-tc)*(in-go*out) <= (t+Tc-tc) * (2*in-out)/2+Tc*(out/2)
        |	& ( (go = 0) -> l + (Tc-tc)*(in) + (Tc)*(in-out) <= (t+(Tc-tc+Tc))*(2*in-out)/2+Tc*(out/2) )
        | & c>= T*MAXIN-(T-Tc)/2*MAXOUT & c>= Tc*MAXIN
        | & l<= t*MAXIN-(t-Tc)/2*MAXOUT & l>=0 & l<= Tc*MAXIN""".stripMargin.asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  /*=====================================================*
   * Running Example 2a - Automated Robot Cruise Control *
   *=====================================================*/
  "Component-based Automated Robot Cruise Control" should "prove Automated Controller Component" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_rbc.kyx")))

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

  it should "prove Actuator Component" in withMathematica { implicit tool =>
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

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
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


  it should "prove Composition" in withMathematica { implicit tool =>
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

  "Monolithic Automated Robot Cruise Control" should "prove Automated System" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\AutoMono.kyx")))

    val invariant = "0<=sAct&sAct<=S & sAc=sAct & sActTr=sAcTr & 0<=sAcTr&sAcTr<=S".asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  /*==================================================*
   * Running Example 2b - Guided Robot Cruise Control *
   *==================================================*/
  "Component-based Guided Robot Cruise Control" should "prove Guided Controller Component" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_rbc.kyx")))

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

  it should "reuse Actuator Component" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_rbc.kyx")))
    val actCtr: Contract = Contract.load("pt2-actuator.cbcps")

    actCtr shouldBe 'verified
  }

  it should "prove new CPO and Sideconditions" in withMathematica { implicit tool =>
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

  it should "prove Composition" in withMathematica { implicit tool =>
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

  "Monolithic Guided Robot Cruise Control" should "prove Guided System" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\2-cruise\\GuidedMono.kyx")))

    val invariant = "0<=sAct&sAct<=S & sGc=sAct & sActTr=sGcTr & 0<=sGcTr&sGcTr<=S & 0<=sGcUsr & sGcUsr<=S".asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & baseTactic & print("Base case done"),
      print("Use case") & useTactic & print("Use case done"),
      print("Induction step") & stepTactic & printIndexed("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }



  /*==============================================*
   * Running Example 3 - Robot Obstacle Avoidance *
   *==============================================*/
  "Component-based Robot Obstacle Avoidance" should "prove Obstacle-Remote Component" in withMathematica { implicit tool =>
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
      val p = ProofHelper.verify(f, sideTactic, Some("pt-obstacle-remote-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    robCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, sideTactic, Some("pt-robot-side-" + v))
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
    val trainSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](robCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt3-robot-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(obsCtr, robCtr, X, cpo, obsSc, trainSc)

    sysCtr shouldBe 'verified
    println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  "Monolithic Robot Obstacle Avoidance" should "prove System" in withMathematica { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\3-robot\\Mono.kyx")))

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


  /*=====================*
   * Case Study 1 - ETCS *
   *=====================*/
  "Component-based ETCS" should "prove RBC Component" in withMathematica { implicit tool =>
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

    //@todo proves only when notL is disabled in normalize, because diffSolve hides facts
    val trainStepTactic = implyR('R) & chase(1) & normalize(andR('R), skip, skip) & OnAll(diffSolve()('R)) & OnAll(normalize partial) & OnAll(speculativeQE)

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

  "Monolithic ETCS" should "prove System" in withMathematica { implicit tool =>
    val t = Globals.t
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\diss-am\\models\\running\\3-robot\\Mono.kyx")))

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

}

