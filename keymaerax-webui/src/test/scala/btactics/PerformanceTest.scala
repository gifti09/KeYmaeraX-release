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

    acCtr.verifyBaseCase(QE)
    acCtr.verifyUseCase(QE)
    acCtr.verifyStep(master())

    acCtr shouldBe 'verified

    Contract.save(acCtr, "pt1-controller-automated.cbcps")
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

    actCtr.verifyBaseCase(QE)
    actCtr.verifyUseCase(QE)
    actCtr.verifyStep(master())

    actCtr shouldBe 'verified

    Contract.save(actCtr, "pt1-actuator.cbcps")
  }

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val acCtr: Contract = Contract.load("pt1-controller-automated.cbcps")
    val actCtr: Contract = Contract.load("pt1-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sAc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sAcTr".asVariable)
    )

    //CPO
    acCtr.cpo(actCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, master(), Some("pt1-automated-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    acCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, master(), Some("pt1-controller-automated-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    actCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, master(), Some("pt1-actuator-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withMathematica { implicit tool =>
    val acCtr: Contract = Contract.load("pt1-controller-automated.cbcps")
    val actCtr: Contract = Contract.load("pt1-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sAc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sAcTr".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](acCtr.cpo(actCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt1-automated-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val acSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](acCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt1-controller-automated-side-" + v).get
    }
    }.toSeq: _*)
    val actSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](actCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt1-actuator-side-" + v).get
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
      print("Base case") & QE & print("Base case done"),
      print("Use case") & QE & print("Use case done"),
      print("Induction step") & master() & printIndexed("Induction step done")
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

    println("CTR: "+gcCtr.contract())

    gcCtr.verifyBaseCase(QE & print("bc done?"))
    gcCtr.verifyUseCase(QE & print("uc done?"))
    gcCtr.verifyStep(master() & print("step done?"))

    gcCtr shouldBe 'verified

    Contract.save(gcCtr, "pt1-controller-guided.cbcps")
  }

  it should "reuse Actuator Component" in withMathematica { implicit tool =>
    //    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_rbc.kyx")))
    val actCtr: Contract = Contract.load("pt1-actuator.cbcps")

    actCtr shouldBe 'verified
  }

  it should "prove new CPO and Sideconditions" in withMathematica { implicit tool =>
    val gcCtr: Contract = Contract.load("pt1-controller-guided.cbcps")
    val actCtr: Contract = Contract.load("pt1-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sGc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sGcTr".asVariable)
    )

    //CPO
    gcCtr.cpo(actCtr, X).foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, master(), Some("pt1-guided-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    gcCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p = ProofHelper.verify(f, master(), Some("pt1-controller-guided-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
//    actCtr.sideConditions().foreach { case (v, f: Formula) => {
//      val p = ProofHelper.verify(f, master(), Some("pt1-actuator-side-" + v))
//      p shouldBe 'nonEmpty
//      v -> p
//    }
//    }
  }

  it should "prove Composition" in withMathematica { implicit tool =>
    val gcCtr: Contract = Contract.load("pt1-controller-guided.cbcps")
    val actCtr: Contract = Contract.load("pt1-actuator.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("sGc".asVariable) -> Seq("sAct".asVariable),
      Seq("sActTr".asVariable) -> Seq("sGcTr".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](gcCtr.cpo(actCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt1-guided-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val acSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](gcCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt1-controller-guided-side-" + v).get
    }
    }.toSeq: _*)
    val actSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](actCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt1-actuator-side-" + v).get
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
      print("Base case") & QE & print("Base case done"),
      print("Use case") & QE & print("Use case done"),
      print("Induction step") & master() & printIndexed("Induction step done")
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

    obsCtr.verifyBaseCase(QE)
    obsCtr.verifyUseCase(QE)
    obsCtr.verifyStep(master())

    obsCtr shouldBe 'verified

    Contract.save(obsCtr, "pt2-obstacle-remote.cbcps")
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

    robCtr.verifyBaseCase(QE)
    robCtr.verifyUseCase(QE)
    robCtr.verifyStep(master())

    robCtr shouldBe 'verified

    Contract.save(robCtr, "pt2-robot.cbcps")
  }

  it should "prove CPO and Sideconditions" in withMathematica { implicit tool =>
    val obsCtr: Contract = Contract.load("pt2-obstacle-remote.cbcps")
    val robCtr: Contract = Contract.load("pt2-robot.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    //CPO
    obsCtr.cpo(robCtr, X).foreach { case (v, f: Formula) => {
      val p=ProofHelper.verify(f, master(), Some("pt2-cpo-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }

    //Side Condition
    obsCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p=ProofHelper.verify(f, master(), Some("pt2-obstacle-remote-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
    robCtr.sideConditions().foreach { case (v, f: Formula) => {
      val p=ProofHelper.verify(f, master(), Some("pt2-robot-side-" + v))
      p shouldBe 'nonEmpty
      v -> p
    }
    }
  }

  it should "prove Composition" in withMathematica { implicit tool =>
    val obsCtr: Contract = Contract.load("pt2-obstacle-remote.cbcps")
    val robCtr: Contract = Contract.load("pt2-robot.cbcps")

    //Port Connections
    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    //CPO
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](obsCtr.cpo(robCtr, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("pt2-cpo-" + v).get
    }
    }.toSeq: _*)

    //Side Condition
    val acSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](obsCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt2-obstacle-remote-side-" + v).get
    }
    }.toSeq: _*)
    val actSc: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](robCtr.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma("pt2-robot-side-" + v).get
    }
    }.toSeq: _*)

    //Compose
    val sysCtr: Contract = Contract.composeWithLemmas(obsCtr, robCtr, X, cpo, acSc, actSc)

    sysCtr shouldBe 'verified
        println("CTR: " + sysCtr.contract())
    //    println("DONE? " + proveBy(sysCtr.contract(), sysCtr.tactic(sysCtr.baseCaseLemma.get,sysCtr.useCaseLemma.get, sysCtr.stepLemma.get)).isProved)
  }

  "Monolithic Robot Obstacle Avoidance" should "prove System" in withMathematica { implicit tool =>
    val t = Globals.runT

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
      print("Base case") & QE & print("Base case done"),
      print("Use case") & QE & print("Use case done"),
      print("Induction step") & master() & printIndexed("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }
}
