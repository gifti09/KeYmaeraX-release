package cbcps

import java.io.FileInputStream
import java.time.DayOfWeek

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentPositionTactic, Find, PosInExpr}
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedAxioms, Simplifier, SimplifierV2, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{DifferentialProgram, ODESystem, Program}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{printIndexed, _}
import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable._
import scala.collection.mutable.LinkedHashMap
import scala.collection.{immutable, mutable}

/**
  * Created by Andreas on 19.11.2015.
  */
object Tester {


  def main(args: Array[String]) {
    test()
  }

  // --- HELPER METHODS ---

  def testRobixFormula() = {
    /*
    val f = "v_0>=0 &\n A>=0 &\n B>0 & \n V>=0 & \n ep>0 &\n -B<=a & \n a<=A & \n -(x_0-xoIn_0)>v_0^2/(2*B)+V*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V)) & \n -(t-tOld)*(v_0+a*(t-tOld)-a/2*(t-tOld))<=x-x_0 & x-x_0<=(t-tOld)*(v_0+a*(t-tOld)-a/2*(t-tOld)) & \n 0<=t-tOld &\n t-tOld<=ep & \n t<=ep & \n v_0+a*(t-tOld)>=0 &\n -V*(t-tOld)<=xoIn-xoIn_0 &\n xoIn-xoIn_0<=V*(t-tOld) &\n x_0-xoIn_0 < 0 &\n x-xoIn < 0\n  ->  -(x-xoIn)>(v_0+a*(t-tOld))^2/(2*B)+V*((v_0+a*(t-tOld))/B)".asFormula

    TactixLibrary.proveBy(
      f,
      implyR('R) & (andL('L) *) & printIndexed("before rt")& replaceTransform("ep".asVariable,"t-tOld".asTerm)(-8) & printIndexed("after rt")& speculativeQE
      //      implyR('R) & (andL('L) *) & abs(-9, 0 :: Nil) & abs(1, 1 :: 0 :: Nil) & normalize(betaRule,skip,skip) & printIndexed("abs done")
      //        & onAll(exhaustiveEqL2R(true)(-22) & exhaustiveEqL2R(true)(-20) & exhaustiveEqL2R(true)(-10) & exhaustiveEqL2R(true)(-6)) & printIndexed("L2R done") & onAll(speculativeQE & print("QE done for branch")) & print("end")
    )
  */

    val f = " true\n   & ep>0\n   & A>=0\n   & B>0\n   & 0<=vf\n   & xf < xlIn_0\n   & xf+vf^2/(2*B) < xlIn_0+vlIn_0^2/(2*B)\n   & 0<=t-tOld_0\n   & t-tOld_0<=ep\n   & 0<=vlIn_0\n   & -B*(t-tOld_0)<=vlIn_0-vlIn0_0\n   & vlIn_0-vlIn0_0<=A*(t-tOld_0)\n   & xlIn_0-xlIn0_0>=(vlIn_0+vlIn0_0)/2*(t-tOld_0)\n   & xlIn0=xlIn_0\n   & vlIn0=vlIn_0\n   & xf+vf^2/(2*B)+(A/B+1)*(A/2*ep^2+ep*vf) < xlIn_0+vlIn_0^2/(2*B)\n   & -B<=af\n   & af<=A\n   & tOld=t\n   & t_>=0\n   & af*t_+vf>=0&t_+t-tOld<=ep\n   & 0<=vlIn\n   & -B*(t_+t-tOld)<=vlIn-vlIn0\n   & vlIn-vlIn0<=A*(t_+t-tOld)&xlIn-xlIn0>=(vlIn+vlIn0)/2*(t_+t-tOld)\n-> af/2*t_^2+vf*t_+xf+(af*t_+vf)^2/(2*B) < xlIn+vlIn^2/(2*B)".asFormula

    println("proved? " + TactixLibrary.proveBy(
      f,
      implyR('R) & (andL('L) *) & printIndexed("start")
        & exhaustiveEqL2R(true)(-19) & exhaustiveEqL2R(true)(-15) & exhaustiveEqL2R(true)(-14) & printIndexed("l2r done")
        & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE)
        & exhaustiveEqL2R(true)(-24) & printIndexed("t-t removed")
        & hideL(-22) & hideL(-12) & printIndexed("hidden")
        & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE) & print("cut in")
        & QE

      //      implyR('R) & (andL('L) *) & abs(-9, 0 :: Nil) & abs(1, 1 :: 0 :: Nil) & normalize(betaRule,skip,skip) & printIndexed("abs done")
      //        & onAll(exhaustiveEqL2R(true)(-22) & exhaustiveEqL2R(true)(-20) & exhaustiveEqL2R(true)(-10) & exhaustiveEqL2R(true)(-6)) & printIndexed("L2R done") & onAll(speculativeQE & print("QE done for branch")) & print("end")
    ).isProved)

  }

  def testBoxTrue() = {
    val f = "true->[?true;]true".asFormula

    println(TactixLibrary.proveBy(f, implyR('R) & cohide(1) & boxTrue(1)).isProved)
  }

  def testTwoODEAxiom() = {
    val f="[c:=0;{a'=b,b'=a,c'=1&c<10}]c>=0".asFormula

    println(TactixLibrary.proveBy(f, composeb('R) & print("before") & useAt("DGiA", PosInExpr(1::Nil))(1,1::Nil) & print("after") & assignb('R) & master()).isProved)
  }

  def testProofRules() = {
    val f="[x:=*;?x>0]x>0 -> [x:=2;?x>0]x>0".asFormula

    println(TactixLibrary.proveBy(f, implyR & randomb('L)))
  }

  def test() = {
    ProofHelper.initProver
    //Match Test
    //    matchTest("x,x>0&x<10,y,y=0")
    //(Free/Bound) Variable Test
    //    variableTest()
    //Proof Test 1
    //    proofTest("a>0->[{a'=2}]a>0".asFormula, implyR('R) & diffSolve()('R) & QE)
    //Proof Test 2
    //    proofTest(parseToSequent(new FileInputStream("C:/svn-vde/documents/draft/models/robot_X/acc/robixsimplerobot.key")), implyR('R) & andL('L) *@ TheType())
    //Proof Test 3
    //    proofTest("[{t'=1,x'=v,y'=u&x>=1}]x>=0 -> [{t'=1,x'=v,y'=u&x>=1&y>=5}]x>=0".asFormula, implyR(1) & useAt("DW differential weakening")(1, 1 :: Nil))
    //Proof Test 4
    //    proofTest("[{c&H(??)}]p(??) -> [{c&H(??)&r(??)}]p(??)".asFormula, implyR(1) & useAt("DW differential weakening")(1, 1 :: Nil))
    //DifferentialProgram Test
    //    differentialProgramTest()
    //PrettyPrinter tTest
    //    prettyPrinterTest()
    //Lemma Test
    //    lemmaTest()
    //    //Position Test
    //    positionTest()
    //Diff-Match-Test
    //    diffTest()
    //Diff Cut Test
    //    dci()
    //piOutAll Test
    //    piOutAllTest()
    //In Test
    //    inTest()
    //Position search test
    //    posTest()
    //TacticTest
    //    tacticTest()
    //Verify Formula for Robix
    //    testRobixFormula()
    //boxTrue Test
    //    testBoxTrue()
    //Two-ODE Axiom
//    testTwoODEAxiom()
    //Test Proof Rules
    testProofRules()

    //        val t1 = test1(true)
    //        val bt = bigTest(true)
    //        val t2 = test2(true)
    //        val t3 = test3(true)
    //        val td4 = testD4(true)
    //        val bdt = bigTestDelta(true)
    //        val td5 = testD5(true)
    //        val td6 = testD6(true)
    //        val tm7 = testM7(true)
    //        val tmd8 = testMD8(true)

    //    val tr = testRobix(true)
    //        val tetcs = testEtcs(false)

    //    val tllc = testLlc(true)

    //        val trun = testRunning(true)

    println("--- SUMMARY ---")
    println("===============")
    //        println("test1 done? " + t1)
    //        println("bigTest done? " + bt)
    //        println("test2 done? " + t2)
    //        println("test3 done? " + t3)
    //        println("testD4 done? " + td4)
    //        println("bigDeltaTest done? " + bdt)
    //        println("testD5 done? " + td5)
    //        println("testD6 done? " + td6)
    //        println("testM7 done? " + tm7)
    //        println("testMD8 done? " + tmd8)
    //        println("testRunning done? " + trun)

    //    println("testRobix done? " + tr)
    //    println("testEtcs done? " + tetcs)
    //        println("testLlc done? " + tllc)

    ProofHelper.shutdownProver
    System.exit(0)
  }

  def testD6(initialize: Boolean = true, name: String = "test6"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-C1", "?x>0;?a=6;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-C2", "u:=-1;?y<=42&y0<=42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = Interface.SinglePortInterface(mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("a".asVariable -> "a>5".asFormula, "b".asVariable -> "b>0".asFormula), mutable.LinkedHashMap("a".asVariable -> "a0".asVariable))
      val i2 = Interface.SinglePortInterface(mutable.LinkedHashMap("y".asVariable -> "y>0".asFormula, "z".asVariable -> "z>0".asFormula), mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap.empty[Variable, Variable])
      val ctr1 = new DelayContract(c1, i1, "a=6 & b>0 & b<5& x>42".asFormula, "b<a".asFormula, "a>5 & b>0 & b<5".asFormula)
      val ctr2 = new DelayContract(c2, i2, "true".asFormula, "true".asFormula, "true".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        println("f1: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        println("f2: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("y".asVariable) -> Seq("b".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testD5(initialize: Boolean = true, name: String = "test5"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-C1", "?x>0;?a=6;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-C2", "u:=-1;?y<=42&y0<=42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = Interface.SinglePortInterface(mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("a".asVariable -> "a>5".asFormula, "b".asVariable -> "b<1".asFormula), mutable.LinkedHashMap("a".asVariable -> "a0".asVariable))
      val i2 = Interface.SinglePortInterface(mutable.LinkedHashMap("y".asVariable -> "y>0".asFormula), mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("y".asVariable -> "y0".asVariable))
      val ctr1 = new DelayContract(c1, i1, "a=6 & b<1 & x>42".asFormula, "b<a".asFormula, "a>5 & b<1".asFormula)
      val ctr2 = new DelayContract(c2, i2, "true".asFormula, "true".asFormula, "true".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        println("f1: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        println("f2: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("y".asVariable) -> Seq("a".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testD4(initialize: Boolean = true, name: String = "test4"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-C1", "?x>0;?a=6;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-C2", "u:=-1;?y<=42&y0<=42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = Interface.SinglePortInterface(mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("a".asVariable -> "a>5".asFormula, "b".asVariable -> "b<1".asFormula), mutable.LinkedHashMap("a".asVariable -> "a0".asVariable))
      val i2 = Interface.SinglePortInterface(mutable.LinkedHashMap("y".asVariable -> "y>0".asFormula), mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("y".asVariable -> "y0".asVariable))
      val ctr1 = new DelayContract(c1, i1, "a=6 & b=0 & x>42".asFormula, "b<a".asFormula, "a>5 & b<1".asFormula)
      val ctr2 = new DelayContract(c2, i2, "true".asFormula, "true".asFormula, "true".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        println("f1: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        println("f2: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      //      "y".asVariable -> "a".asVariable
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo1-" + v).get
    }
    }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def test1(initialize: Boolean = true, name: String = "test1"): Boolean = {

    if (initialize) {
      //Component 1
      val c1: Component = {
        new Component(name + "-C1", //Name
          "a:=a+y;".asProgram, //Control
          "a'=0".asProgram.asInstanceOf[ODESystem]) //Plant
      }
      //Interface 1
      val i1: Interface = {
        Interface.SinglePortInterface(
          LinkedHashMap("y".asVariable -> "y>=0".asFormula), //In
          LinkedHashMap("out1".asVariable -> "out1=42".asFormula), //Out
          mutable.LinkedHashMap.empty[Variable, Variable] //Pre
        )
      }
      //Contract 1
      val ctr1: Contract = new DelayContract(c1, i1,
        "a=0&y>=0&out1=42".asFormula, //Pre
        "a>=0".asFormula, //Post
        "a>=0&y>=0&out1=42".asFormula) //Invariant
      println("Contract(C1,I1): " + ctr1.contract())
      //Verify Contract 1 from scratch
      verifyContract1(ctr1)
      //Verify Contract 1 from Lemmas
      //        verifyContract1Lemma(ctr1)
      //Save Contract 1
      Contract.save(ctr1, name + "-contract1.cbcps")

      //Component 2
      val c2: Component = {
        new Component(name + "-C2", //Name
          "{{x:=1;}++{x:=3;}}".asProgram, //Control
          "x'=1&x<=2".asProgram.asInstanceOf[ODESystem]) //Plant
      }
      //Interface 2
      val i2: Interface = {
        Interface.SinglePortInterface(
          LinkedHashMap("in2".asVariable -> "in2=42".asFormula), //In
          LinkedHashMap("x".asVariable -> "x>=1".asFormula), //Out
          mutable.LinkedHashMap.empty[Variable, Variable] //Pre
        )
      }
      //Contract 2
      val ctr2: Contract = new DelayContract(c2, i2,
        "x=2&in2=42".asFormula, //Pre
        "true".asFormula, //Post
        "x<=3&x>=1&in2=42".asFormula) //Invariant
      println("Contract(C2,I2): " + ctr2.contract())
      //Verify Contract 2 from scratch
      verifyContract2(ctr2)
      //Verify Contract 2 from Lemmas
      //        verifyContract2Lemma(ctr2)
      //Save Contract 2
      Contract.save(ctr2, name + "-contract2.cbcps")

      //Everything Verified?
      println("Contract(C1,I1) verified? " + ctr1.isVerified())
      println("Contract(C2,I2) verified? " + ctr2.isVerified())
    }

    val lc1 = Contract.load(name + "-contract1.cbcps")
    val lc2 = Contract.load(name + "-contract2.cbcps")
    println("Contract(C1,I1) = " + lc1.contract())
    println("Loaded Contract(C1,I1) verified? " + lc1.isVerified())
    println("Contract(C2,I2) = " + lc2.contract())
    println("Loaded Contract(C2,I2) verified? " + lc2.isVerified())

    val X = mutable.LinkedHashMap(
      Seq("y".asVariable) -> Seq("x".asVariable)
    )

    var cpoT: mutable.Map[(Seq[Variable], Seq[Variable]), BelleExpr] = mutable.Map.empty
    cpoT += (Seq("y".asVariable), Seq("x".asVariable)) -> (implyR('R) & assignb('R) & implyR('R) & QE)
    //    println("CPO verified? " + cpoT.forall { case (m, t) => TactixLibrary.proveBy(lc1.cpo(lc2, X)(m), t).isProved })

    val sc1 = lc1.sideConditions()
    val sc1T: mutable.Map[Seq[Variable], BelleExpr] = sc1.map((e) => (e._1, master()))
    println("sc1: " + sc1)
    //    println("SC1 verified? " + TactixLibrary.proveBy(lc1.sideCondition(), sc1T).isProved)

    val sc2 = lc2.sideConditions()
    val sc2T: mutable.Map[Seq[Variable], BelleExpr] = sc2.map((e) => (e._1, master()))
    println("sc2: " + sc2)
    //    println("SC2 verified? " + TactixLibrary.proveBy(lc2.sideCondition(), sc2T).isProved)

    println("Composing...")
    val ctr3 = Contract.composeWithSideTactics(lc1, lc2, X, cpoT, sc1T, sc2T)
    println("Contract(C1,I1)=\n\t" + lc1.contract())
    println("Contract(C2,I2)=\n\t" + lc2.contract())
    println("Contract( (C1,I1)||(C2,I2) )=\n\t" + ctr3.contract())
    println("Contract (C3,I3) verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def test3(initialize: Boolean = true, name: String = "test3"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-C1", "?x>0;a:=42;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-C2", "u:=-1;?y<42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = Interface.SinglePortInterface(mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("a".asVariable -> "a>5".asFormula, "b".asVariable -> "b<1".asFormula), mutable.LinkedHashMap.empty[Variable, Variable])
      val i2 = Interface.SinglePortInterface(mutable.LinkedHashMap("y".asVariable -> "y>0".asFormula), mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap.empty[Variable, Variable])
      val ctr1 = new DelayContract(c1, i1, "a=6 & b=0 & x>42".asFormula, "b<a".asFormula, "a>5 & b<1".asFormula)
      val ctr2 = new DelayContract(c2, i2, "true".asFormula, "true".asFormula, "true".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      //      "y".asVariable -> "a".asVariable
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def test2(initialize: Boolean = true, name: String = "test2"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-D1", "?x>0;a:=42;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-D2", "u:=-1;?y<42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = Interface.SinglePortInterface(mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("a".asVariable -> "a>5".asFormula, "b".asVariable -> "b<1".asFormula), mutable.LinkedHashMap.empty[Variable, Variable])
      val i2 = Interface.SinglePortInterface(mutable.LinkedHashMap("y".asVariable -> "y>0".asFormula), mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap.empty[Variable, Variable])
      val ctr1 = new DelayContract(c1, i1, "a=6 & b=0 & x>42".asFormula, "b<a".asFormula, "a>5 & b<1".asFormula)
      val ctr2 = new DelayContract(c2, i2, "true".asFormula, "true".asFormula, "true".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap(
      Seq("y".asVariable) -> Seq("a".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def bigTestDelta(initialize: Boolean = true, name: String = "bigTestDelta"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-BD1", "?ctr1>0;".asProgram, ODESystem("p1'=1".asDifferentialProgram, "p1<1".asFormula))
      val c2 = new Component(name + "-BD2", "?ctr2<42;".asProgram, ODESystem("p2'=1".asDifferentialProgram, "p2<1".asFormula))
      val i1 = Interface.SinglePortInterface(
        mutable.LinkedHashMap("r".asVariable -> "r>0".asFormula, "i1i1".asVariable -> "i1i1>0".asFormula, "s".asVariable -> "s>0".asFormula, "i1i2".asVariable -> "i1i2>0".asFormula),
        mutable.LinkedHashMap("a_".asVariable -> "a_>0".asFormula, "i1o1".asVariable -> "i1o1>0".asFormula, "b_".asVariable -> "b_>0".asFormula, "i1o2".asVariable -> "i1o2>0".asFormula),
        mutable.LinkedHashMap("r".asVariable -> "r0".asVariable, "a_".asVariable -> "a_0".asVariable, "i1i1".asVariable -> "i1i10".asVariable)
      )
      val i2 = Interface.SinglePortInterface(
        mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "i2i1".asVariable -> "i2i1>0".asFormula, "b".asVariable -> "b>0".asFormula, "i2i2".asVariable -> "i2i2>0".asFormula),
        mutable.LinkedHashMap("r_".asVariable -> "r_>0".asFormula, "i2o1".asVariable -> "i2o1>0".asFormula, "s_".asVariable -> "s_>0".asFormula, "i2o2".asVariable -> "i2o2>0".asFormula),
        mutable.LinkedHashMap("r_".asVariable -> "r_0".asVariable, "a".asVariable -> "a0".asVariable, "i2o2".asVariable -> "i2o20".asVariable)
      )
      val ctr1 = new DelayContract(c1, i1, "a_=1 & b_=1 & i1o1=1 & i1o2=1".asFormula, "true".asFormula, "a_=1 & b_=1 & i1o1=1 & i1o2=1".asFormula)
      val ctr2 = new DelayContract(c2, i2, "r_=1 & s_=1 & i2o1=1 & i2o2=1".asFormula, "true".asFormula, "r_=1 & s_=1 & i2o1=1 & i2o2=1".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      ctr1.verifyBaseCase(QE)
      ctr1.verifyUseCase(QE)
      ctr1.verifyStep(master())
      ctr2.verifyBaseCase(QE)
      ctr2.verifyUseCase(QE)
      ctr2.verifyStep(master())
      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      Contract.save(ctr1, name + "-bigd1.cbcps")
      Contract.save(ctr2, name + "-bigd2.cbcps")
      println("Saved both contracts!")
    }
    val lctr1 = Contract.load(name + "-bigd1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-bigd2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side contision
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap(
      Seq("r".asVariable) -> Seq("r_".asVariable),
      Seq("s".asVariable) -> Seq("s_".asVariable),
      Seq("a".asVariable) -> Seq("a_".asVariable),
      Seq("b".asVariable) -> Seq("b_".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        println("CPO: " + f)
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
      //      lctr2.cpo(lctr1, X).foreach { case (v, f: Formula) => {
      //        println("CPO2-1: "+f)
      //        v -> ProofHelper.verify(f, master(), Some("bd-cpo2-1-" + v))
      //      }
      //      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)
    //    ++
    //      mutable.Map[(Variable, Variable), Lemma](lctr2.cpo(lctr1, X).map { case (v, f: Formula) => {
    //        v -> Utility.loadLemma("bd-cpo2-1-" + v).get
    //      }
    //      }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def bigTest(initialize: Boolean = true, name: String = "bigTest"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-B1", "?ctr1>0;".asProgram, ODESystem("p1'=1".asDifferentialProgram, "p1<1".asFormula))
      val c2 = new Component(name + "-B2", "?ctr2<42;".asProgram, ODESystem("p2'=1".asDifferentialProgram, "p2<1".asFormula))
      val i1 = Interface.SinglePortInterface(mutable.LinkedHashMap("r".asVariable -> "r>0".asFormula, "i1i1".asVariable -> "i1i1>0".asFormula, "s".asVariable -> "s>0".asFormula, "i1i2".asVariable -> "i1i2>0".asFormula), mutable.LinkedHashMap("a_".asVariable -> "a_>0".asFormula, "i1o1".asVariable -> "i1o1>0".asFormula, "b_".asVariable -> "b_>0".asFormula, "i1o2".asVariable -> "i1o2>0".asFormula), mutable.LinkedHashMap.empty[Variable, Variable])
      val i2 = Interface.SinglePortInterface(mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "i2i1".asVariable -> "i2i1>0".asFormula, "b".asVariable -> "b>0".asFormula, "i2i2".asVariable -> "i2i2>0".asFormula), mutable.LinkedHashMap("r_".asVariable -> "r_>0".asFormula, "i2o1".asVariable -> "i2o1>0".asFormula, "s_".asVariable -> "s_>0".asFormula, "i2o2".asVariable -> "i2o2>0".asFormula), mutable.LinkedHashMap.empty[Variable, Variable])
      val ctr1 = new DelayContract(c1, i1, "a_=1 & b_=1 & i1o1=1 & i1o2=1".asFormula, "true".asFormula, "a_=1 & b_=1 & i1o1=1 & i1o2=1".asFormula)
      val ctr2 = new DelayContract(c2, i2, "r_=1 & s_=1 & i2o1=1 & i2o2=1".asFormula, "true".asFormula, "r_=1 & s_=1 & i2o1=1 & i2o2=1".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      ctr1.verifyBaseCase(QE)
      ctr1.verifyUseCase(QE)
      ctr1.verifyStep(master())
      ctr2.verifyBaseCase(QE)
      ctr2.verifyUseCase(QE)
      ctr2.verifyStep(master())
      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      Contract.save(ctr1, name + "-big1.cbcps")
      Contract.save(ctr2, name + "-big2.cbcps")
      println("Saved both contracts!")
    }
    val lctr1 = Contract.load(name + "-big1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-big2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side contision
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap(
      Seq("r".asVariable) -> Seq("r_".asVariable),
      Seq("s".asVariable) -> Seq("s_".asVariable),
      Seq("a".asVariable) -> Seq("a_".asVariable),
      Seq("b".asVariable) -> Seq("b_".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testM7(initialize: Boolean = true, name: String = "test7"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-C1", "?x>0;a:=42;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-C2", "u:=-1;?y<42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = new Interface(mutable.LinkedHashMap(Seq("mi1".asVariable, "mi2".asVariable, "mi3".asVariable) -> "mi1+mi2+mi3=0".asFormula, Seq("zmi1".asVariable, "zmi2".asVariable) -> "omi1>omi2".asFormula),
        mutable.LinkedHashMap(Seq("a".asVariable) -> "a>5".asFormula, Seq("b".asVariable) -> "b<1".asFormula))
      val i2 = new Interface(mutable.LinkedHashMap(Seq("y".asVariable) -> "y>0".asFormula),
        mutable.LinkedHashMap(Seq("mo1".asVariable, "mo2".asVariable, "mo3".asVariable) -> "mo1+mo2+mo3=0".asFormula))
      val ctr1 = new DelayContract(c1, i1, "a=6 & b=0 & x>42 & mi1+mi2+mi3=0".asFormula, "b<a".asFormula, "a>5 & b<1 & mi1+mi2+mi3=0".asFormula)
      val ctr2 = new DelayContract(c2, i2, "mo1+mo2+mo3=0".asFormula, "true".asFormula, "mo1+mo2+mo3=0".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("y".asVariable) -> Seq("a".asVariable),
      Seq("mi1".asVariable, "mi2".asVariable, "mi3".asVariable) -> Seq("mo1".asVariable, "mo2".asVariable, "mo3".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testMD8(initialize: Boolean = true, name: String = "test8"): Boolean = {
    if (initialize) {
      val c1 = new Component(name + "-C1", "?x>0;a:=42;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name + "-C2", "u:=-1;?y<42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = new Interface(
        mutable.LinkedHashMap(Seq("mi1".asVariable, "mi2".asVariable, "mi3".asVariable) -> "mi1+mi2+mi3=0".asFormula, Seq("zmi1".asVariable, "zmi2".asVariable) -> "zmi1>zmi2".asFormula),
        mutable.LinkedHashMap(Seq("a".asVariable) -> "a>5".asFormula, Seq("b".asVariable) -> "b<1".asFormula, Seq("x1d1".asVariable, "x1d2".asVariable) -> "x1d1+x1d2>=x1d10+x1d20".asFormula),
        mutable.LinkedHashMap(Seq("x1d1".asVariable, "x1d2".asVariable) -> Seq("x1d10".asVariable, "x1d20".asVariable))
      )
      val i2 = new Interface(
        mutable.LinkedHashMap(Seq("y".asVariable) -> "y>0".asFormula, Seq("x2d1".asVariable, "x2d2".asVariable) -> "x2d1+x2d2>=x2d10+x2d20".asFormula),
        mutable.LinkedHashMap(Seq("mo1".asVariable, "mo2".asVariable, "mo3".asVariable) -> "mo1+mo2+mo3=0".asFormula),
        mutable.LinkedHashMap(Seq("x2d1".asVariable, "x2d2".asVariable) -> Seq("x2d10".asVariable, "x2d20".asVariable))
      )
      val ctr1 = new DelayContract(c1, i1, "a=6 & b=0 & x>42 & mi1+mi2+mi3=0 & x1d1+x1d2>=x1d10+x1d20".asFormula, "b<a".asFormula, "a>5 & b<1 & mi1+mi2+mi3=0 & x1d1+x1d2>=x1d10+x1d20".asFormula)
      val ctr2 = new DelayContract(c2, i2, "mo1+mo2+mo3=0 & x2d1+x2d2>=x2d10+x2d20".asFormula, "true".asFormula, "mo1+mo2+mo3=0 & x2d1+x2d2>=x2d10+x2d20".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println("ctr1-step NOT verified!")
      if (ctr2.verifyBaseCase(QE).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("y".asVariable) -> Seq("a".asVariable),
      Seq("mi1".asVariable, "mi2".asVariable, "mi3".asVariable) -> Seq("mo1".asVariable, "mo2".asVariable, "mo3".asVariable),
      Seq("x2d1".asVariable, "x2d2".asVariable) -> Seq("x1d1".asVariable, "x1d2".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testRobix(initialize: Boolean = true, name: String = "robix"): Boolean = {
    if (initialize) {

      val t = Globals.runT

      //COMPONENT 1 - ROBOT
      val c1 = new Component(name + "-Robot",
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
      val i1 = new Interface(
        mutable.LinkedHashMap(
          Seq("xoIn".asVariable) -> ("-V*" + t + " <= xoIn-xoIn0 & xoIn-xoIn0 <= V*" + t).asFormula,
          Seq("yoIn".asVariable) -> ("-V*" + t + " <= yoIn-yoIn0 & yoIn-yoIn0 <= V*" + t).asFormula
        ),
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(Seq("xoIn".asVariable) -> Seq("xoIn0".asVariable), Seq("yoIn".asVariable) -> Seq("yoIn0".asVariable))
      )
      val ctr1 = new DelayContract(c1, i1,
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
           |          | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula)

      println("Ctr1 - Robot: " + ctr1.contract())
      println("ProofGoals1:\n" + ctr1.proofGoals().mkString("\n"))

      def di1(a: String, t: String): DependentPositionTactic = diffInvariant(
        s"0<=$t".asFormula,
        "dx^2 + dy^2 = 1".asFormula,
        s"v = old(v) + $a*($t)".asFormula,
        s"-($t) * (v - $a/2*($t)) <= x - old(x) & x - old(x) <= ($t) * (v - $a/2*($t))".asFormula,
        s"-($t) * (v - $a/2*($t)) <= y - old(y) & y - old(y) <= ($t) * (v - $a/2*($t))".asFormula)

      val dw1: BelleExpr = exhaustiveEqR2L(hide = true)('Llast) * 3 /* 3 old(...) in DI */ & (andL('_) *) &
        print("Before diffWeaken") & dW(1) & print("After diffWeaken")

      def accArithTactic1: BelleExpr = (alphaRule *) & printIndexed("Before replaceTransform") &
        replaceTransform("ep".asTerm, "(t-tOld)".asTerm)(-10) & print("After replaceTransform") &
        speculativeQE & print("Proved acc arithmetic")

      val st1 = print("Induction step") & (andL('L) *) & chase(1) & print("After chase") & normalize() /* TODO normalize(choiceb('R) | composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) */ & printIndexed("After normalize") < (
        print("Braking branch") & di1("-B", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize() /* TODO normalize(choiceb('R) | composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) */  & print("After braking normalize") & OnAll(speculativeQE) & print("Braking branch done"),
        print("Stopped branch") & di1("0", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & unfoldProgramNormalize & OnAll(speculativeQE) & print("Stopped branch done"),
        print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula))) &
          di1("a", "t-tOld")(1) & print("After DI") & dw1 & print("After DW") & normalize() /* TODO normalize(betaRule, skip, skip) */ & print("After acc normalize") & OnAll(hideFactsAbout("dx", "dy", "k", "k_0") partial) < (
          hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic1,
          hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic1
        ) & print("Acceleration branch done")
      ) & print("Induction step done")

      val bct1 = print("Base case...") & (andL('L) *) & speculativeQE & print("Base case done")
      val uct1 = print("Use case...") & (andL('L) *) & speculativeQE & print("Use case done")
      //      val st1 = print("Induction step") & chase(1) & normalize(composeb('R) | assignb('R), skip, skip) & printIndexed("After normalize") &
      //        chase(1) & normalize(andR('R), skip, skip) & printIndexed("After normalize2") < (
      //        print("Braking branch") &
      //          normalize(composeb('R) | andR('R) | randomb('R) | testb('R) | implyR('R), skip, skip) & printIndexed("After normalize brake1") &
      //          //          normalize(andR('R) | randomb('R) | testb('R) | implyR('R) | assignb('R), skip, skip) & printIndexed("After normalize brake2") &
      //          di1("-B")(1) & dw1 &
      //          OnAll(speculativeQE) & print("Braking branch done"),
      //        print("Stopped branch") & di1("0")(1) & dw1 & normalize(andR('R), skip, skip) & OnAll(speculativeQE) & print("Stopped branch done"),
      //        print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula))) &
      //          di1("a")(1) & dw1 & normalize(betaRule, skip, skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) < (
      //          hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic1,
      //          hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic1
      //          ) & print("Acceleration branch done")
      //        )

      if (ctr1.verifyBaseCase(bct1).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(uct1).isEmpty)
        println("ctr1-useCase NOT verified!")
      //      if (ctr1.verifyStep(st1).isEmpty)
      //        println("ctr1-step NOT verified!")


      //COMPONENT 2 - OBSTACLE
      val c2 = new Component(name + "-Obstacle",
        """dxo :=*;
          |dyo :=*;
          |?dxo^2 + dyo^2 <= V^2;""".stripMargin.asProgram,
        ODESystem(
          """xo' = dxo,
            |yo' = dyo""".stripMargin.asDifferentialProgram)
      )
      val i2 = new Interface(
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
      val ctr2 = new DelayContract(c2, i2,
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
           |& yo-yo0 <= V*$t""".stripMargin.asFormula)

      println("Ctr2 - Obstacle: " + ctr2.contract())
      println("ProofGoals2:\n" + ctr2.proofGoals().mkString("\n"))

      val bct2 = print("Base case...") & speculativeQE & print("Base case done")
      val uct2 = print("Use case...") & speculativeQE & print("Use case done")
      val st2 = print("Induction step") & chase(1) & normalize() /* TODO normalize(composeb('R) | assignb('R), skip, skip) */ & printIndexed("After normalize1") &
        chase(1) & unfoldProgramNormalize & printIndexed("After normalize2") &
        solve('R) & master()

      if (ctr2.verifyBaseCase(bct2).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(uct2).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(st2).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      //      require(ctr1.isVerified(), "ctr1 must be verified!")
      //      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded Robot! verified? " + lctr1.isVerified())
    println("LCtr1-Robot: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded Obstacle! verified? " + lctr2.isVerified())
    println("LCtr2-Obstacle: " + lctr2.contract())

    println("verify obstacle step test: " + TactixLibrary.proveBy(lctr2.proofGoals()(2), TactixLibrary.by(lctr2.stepLemma.get) & prop))

    if (initialize) {
      val sct = normalize() /* TODO normalize(andL('L) | composeb('R) | assignb('R) | randomb('R) | implyR('R) | testb('R), skip, skip) */ &
        solve('R) & master()
      //Verify lemmas for side conditions
      println("Robot sideConditions: " + lctr1.sideConditions().mkString("\n"))
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, sct, Some(name + "-side1-" + v))
        println("side condition '" + name + "-side1-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
      println("Obstacle sideConditions: " + lctr2.sideConditions().mkString("\n"))
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, sct, Some(name + "-side2-" + v))
        println("side condition '" + name + "-side2-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
    }
    //    Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xoIn".asVariable) -> Seq("xo".asVariable),
      Seq("yoIn".asVariable) -> Seq("yo".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      println("Robix cpo: " + lctr1.cpo(lctr2, X).mkString("\n"))
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
        println("cpo '" + name + "-cpo-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, null, null, null, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testEtcs(initialize: Boolean = true, name: String = "etcs"): Boolean = {
    if (initialize) {

      val t = Globals.runT

      //COMPONENT 1 - RBC
      val c1 = new Component(name + "-rbc",
        (
          """state := drive; m :=*; d :=*; vdes :=*; ?d >= 0 & d0^2 - d^2 <= 2*b*(m-m0) & vdes >= 0;
            |++ state := brake;"""
          ).stripMargin.asProgram,
        ODESystem("H'=0".asDifferentialProgram)
      )
      val i1 = new Interface(
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(
          Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable) -> ("(state=brake & m0=m & d0=d) | (state=drive & d >= 0 & d0^2 - d^2 <= 2*b*(m-m0) & vdes >= 0)").asFormula
        ),
        mutable.LinkedHashMap(Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable) -> Seq("state0".asVariable, "m0".asVariable, "d0".asVariable, "vdes0".asVariable))
      )
      val ctr1 = new DelayContract(c1, i1,
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
      println("Ctr1 - rbc: " + ctr1.contract())
      println("ProofGoals1:\n" + ctr1.proofGoals().mkString("\n"))

      val bct1 = print("Base case") & QE & print("Base case done")
      val uct1 = print("Use case") & QE & print("Use case done")
      val st1 = print("Induction step") & implyR('R) & (andL('L) *) & print("Induction step Go...") &
        chase(1) & unfoldProgramNormalize & print("chased and normalized...") &
        OnAll(solve(1) partial) & print("diffsolved...") &
        OnAll(speculativeQE) & printIndexed("Induction step done")


      if (ctr1.verifyBaseCase(bct1).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(uct1).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(st1).isEmpty)
        println("ctr1-step NOT verified!")


      //COMPONENT 2 - TRAIN
      val c2 = new Component(name + "-train",
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
      val i2 = new Interface(
        mutable.LinkedHashMap(
          Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> ("(stateIn=brake & mIn0=mIn & dIn0=dIn) | (stateIn=drive & dIn >= 0 & dIn0^2 - dIn^2 <= 2*b*(mIn-mIn0) & vdesIn >= 0)").asFormula
        ),
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("stateIn0".asVariable, "mIn0".asVariable, "dIn0".asVariable, "vdesIn0".asVariable))
      )
      val ctr2 = new DelayContract(c2, i2,
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

      println("Ctr2 - Train: " + ctr2.contract())
      println("ProofGoals2:\n" + ctr2.proofGoals().mkString("\n"))


      val bct2 = print("Base case") & master() & print("Base case done")
      val uct2 = print("Use case") & master() & print("Use case done")
      //@todo proves only when notL is disabled in normalize, because diffSolve hides facts
      val st2 = print("Induction step") & implyR('R) & chase(1) & unfoldProgramNormalize & printIndexed("WTF?") & OnAll(solve('R) & print("Foo") partial) &
        printIndexed("After diffSolve") & OnAll(normalize partial) & printIndexed("After normalize") & OnAll(speculativeQE) & printIndexed("Induction step done")


      if (ctr2.verifyBaseCase(bct2).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(uct2).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(st2).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      println("Ctr2 verified? " + ctr2.isVerified())

      //      require(ctr1.isVerified(), "ctr1 must be verified!")
      //      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded Robot! verified? " + lctr1.isVerified())
    println("LCtr1-Robot: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded Obstacle! verified? " + lctr2.isVerified())
    println("LCtr2-Obstacle: " + lctr2.contract())

    if (initialize) {
      val sct = print("sideT") & master()
      implyR('R) & (andL('L) *) & print("sideT - implyR/andL") &
        chase(1) & print("sideT - chased") &
        normalize() /* TODO normalize(andL('L) | composeb('R) | assignb('R) | randomb('R) | implyR('R) | testb('R) | allR('R), skip, skip) */ & print("sideT - normalized") &
        solve('R) & master()
      //Verify lemmas for side conditions
      println("Robot sideConditions: " + lctr1.sideConditions().mkString("\n"))
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, sct, Some(name + "-side1-" + v))
        println("side condition '" + name + "-side1-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
      println("Obstacle sideConditions: " + lctr2.sideConditions().mkString("\n"))
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, sct, Some(name + "-side2-" + v))
        println("side condition '" + name + "-side2-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("stateIn".asVariable, "mIn".asVariable, "dIn".asVariable, "vdesIn".asVariable) -> Seq("state".asVariable, "m".asVariable, "d".asVariable, "vdes".asVariable))

    if (initialize) {
      //Verify lemmas for cpo
      println("Robix cpo: " + lctr1.cpo(lctr2, X).mkString("\n"))
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
        println("cpo '" + name + "-cpo-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, null, null, null, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testLlc(initialize: Boolean = true, name: String = "llc"): Boolean = {
    val t = Globals.runT

    if (initialize) {

      //COMPONENT 1 - LEADER
      val c1 = new Component(name + "-leader",
        "al :=*; ?-B <= al & al <= A;".asProgram,
        ODESystem("xl' = vl, vl' = al".asDifferentialProgram, "vl >= 0".asFormula)
      )
      val i1 = new Interface(
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(
          Seq("xl".asVariable, "vl".asVariable) -> (s"0 <= vl & -B*$t <= vl-vl0 & vl-vl0 <= A*$t & xl-xl0 >= (vl+vl0)/2*$t").asFormula
        ),
        mutable.LinkedHashMap(Seq("xl".asVariable, "vl".asVariable) -> Seq("xl0".asVariable, "vl0".asVariable))
      )
      val ctr1 = new DelayContract(c1, i1,
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
      println("Ctr1 - leader: " + ctr1.contract())

      val bct1 = print("Base case") & QE & print("Base case done")
      val uct1 = print("Use case") & QE & print("Use case done")
      val st1 = print("Induction step") & master() & printIndexed("Induction step done")


      if (ctr1.verifyBaseCase(bct1).isEmpty)
        println("ctr1-baseCase NOT verified!")
      if (ctr1.verifyUseCase(uct1).isEmpty)
        println("ctr1-useCase NOT verified!")
      if (ctr1.verifyStep(st1).isEmpty)
        println("ctr1-step NOT verified!")

      println("Ctr1 verified? " + ctr1.isVerified())
      Contract.save(ctr1, name + "-1.cbcps")

      //COMPONENT 2 - FOLLOWER
      val c2 = new Component(name + "-follower",
        """{
          | af := -B;
          |  ++ ?vf=0; af:=0;
          |  ++ ?xf + vf^2/(2*B) + (A/B+1)*(A/2*ep^2 + ep*vf) < xlIn + vlIn^2/(2*B); af :=*; ?-B <= af & af <= A;
          | }""".stripMargin.asProgram,
        ODESystem(
          "xf' = vf,vf' = af".asDifferentialProgram, s"vf >= 0".asFormula)
      )
      val i2 = new Interface(
        mutable.LinkedHashMap(
          Seq("xlIn".asVariable, "vlIn".asVariable) -> (s"0 <= vlIn & -B*$t <= vlIn-vlIn0 & vlIn-vlIn0 <= A*$t & xlIn-xlIn0 >= (vlIn+vlIn0)/2*$t").asFormula
        ),
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xlIn0".asVariable, "vlIn0".asVariable))
      )
      val ctr2 = new DelayContract(c2, i2,
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

      println("Ctr2 - Follower: " + ctr2.contract())

      val bct2 = print("Base case") & master() & print("Base case done")
      val uct2 = print("Use case") & master() & print("Use case done")
      val st2 = print("Induction step") & implyR('R) & chase(1) & unfoldProgramNormalize & print("after normalize") &
        OnAll(solve(1) partial) < (
          print("Braking branch") & normalize & OnAll(speculativeQE) & print("Braking branch done"),
          print("Stopped branch") & normalize & OnAll(speculativeQE) & print("Stopped branch done"),
          (printIndexed("Acceleration branch")
            & normalize() /* TODO normalize(betaRule, skip, skip) */ < (
            print("branch1") & QE & print("b1 done"),
            printIndexed("branch2")
              & allL("s_".asVariable, "t_".asVariable)(-20) & implyL(-20) < (hide(1) & QE, skip) & andL(-20)
              & exhaustiveEqL2R(true)(-18) & exhaustiveEqL2R(true)(-14) & exhaustiveEqL2R(true)(-13)
              & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE) & exhaustiveEqL2R(true)(-23)
              & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE)
              & hide(-13) & hide(-12) & hide(-6) & QE & print("b2 done"),
            printIndexed("branch3")
              & exhaustiveEqL2R(true)(-18) & exhaustiveEqL2R(true)(-14) & exhaustiveEqL2R(true)(-13) & printIndexed("l2r done")
              & cut("t_+t-t=t_".asFormula) < (skip, hide(1) & QE) & exhaustiveEqL2R(true)(-22) & printIndexed("t-t removed")
              & cut("xf+vf^2/(2*B)+(af/B+1)*(af/2*t_^2+t_*vf) < xlIn_0+vlIn_0^2/(2*B)".asFormula) < (skip, hide(1) & QE)
              & allL("s_".asVariable, "t_".asVariable)(-17) & implyL(-17) < (hide(1) & QE, skip) & andL(-17)
              & hide(-13) & hide(-12) & hide(-6)
              & QE & print("b2 done"),
            print("branch4") & QE & print("b4 done"),
            print("branch5") & QE & print("b5 done")
          )
            ) & print("Acceleration branch done")
        ) & print("Induction step done")


      if (ctr2.verifyBaseCase(bct2).isEmpty)
        println("ctr2-baseCase NOT verified!")
      if (ctr2.verifyUseCase(uct2).isEmpty)
        println("ctr2-useCase NOT verified!")
      if (ctr2.verifyStep(st2).isEmpty)
        println("ctr2-step NOT verified!")

      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded Robot! verified? " + lctr1.isVerified())
    println("LCtr1-Robot: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded Obstacle! verified? " + lctr2.isVerified())
    println("LCtr2-Obstacle: " + lctr2.contract())

    if (initialize) {
      val sct = print("sideT") & master()
      implyR('R) & (andL('L) *) & print("sideT - implyR/andL") &
        chase(1) & print("sideT - chased") &
        normalize() /* TODO normalize(andL('L) | composeb('R) | assignb('R) | randomb('R) | implyR('R) | testb('R) | allR('R), skip, skip) */ & print("sideT - normalized") &
        solve('R) & master()
      //Verify lemmas for side conditions
      println("Robot sideConditions: " + lctr1.sideConditions().mkString("\n"))
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, sct, Some(name + "-side1-" + v))
        println("side condition '" + name + "-side1-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
      println("Obstacle sideConditions: " + lctr2.sideConditions().mkString("\n"))
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, sct, Some(name + "-side2-" + v))
        println("side condition '" + name + "-side2-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("xlIn".asVariable, "vlIn".asVariable) -> Seq("xl".asVariable, "vl".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      println("Robix cpo: " + lctr1.cpo(lctr2, X).mkString("\n"))
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        val p = ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
        println("cpo '" + name + "-cpo-" + v + "' verified? " + p.nonEmpty)
        v -> p
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)

    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, null, null, null, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }

  def testRunning(initialize: Boolean = true, name: String = "running"): Boolean = {
    val t = Globals.runT
    if (initialize) {
      val c1 = new Component(name + "-C1", "d:=*;?abs(d-d0)<=D;so:=*;?(0<=so&so<=S);".asProgram, ODESystem("po'=so".asDifferentialProgram))
      val c2 = new Component(name + "-C2", "{?abs(poIn-pr)>dIn*ep+S*ep;sr:=dIn;} ++ {?abs(poIn-pr)<=dIn*ep+S*ep;sr:=0;}".asProgram, ODESystem("pr'=sr".asDifferentialProgram))
      val i1 = new Interface(
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(Seq("d".asVariable) -> "abs(d-d0)<=D".asFormula, Seq("po".asVariable) -> s"abs(po-po0)<=S*$t".asFormula),
        mutable.LinkedHashMap(Seq("d".asVariable) -> Seq("d0".asVariable), Seq("po".asVariable) -> Seq("po0".asVariable)))
      val i2 = new Interface(
        mutable.LinkedHashMap(Seq("dIn".asVariable) -> "abs(dIn-dIn0)<=D".asFormula, Seq("poIn".asVariable) -> s"abs(poIn-poIn0)<=S*$t".asFormula),
        mutable.LinkedHashMap.empty,
        mutable.LinkedHashMap(Seq("dIn".asVariable) -> Seq("dIn0".asVariable), Seq("poIn".asVariable) -> Seq("poIn0".asVariable), Seq("pr".asVariable) -> Seq("pr0".asVariable)))
      val ctr1 = new DelayContract(c1, i1, And(Globals.initTOld, "D>=0 & d=d0 & S>=0 & po=po0 & so=0".asFormula), True, s"D>=0 & S>=0 & 0<=so&so<=S & abs(d-d0)<=D & abs(po-po0)<=S*$t".asFormula)
      val ctr2 = new DelayContract(c2, i2,
        And(Globals.initTOld, "ep>0 & D>=0 & dIn=dIn0 & S>=0 & poIn=poIn0 & sr=0".asFormula),
        "sr>0 -> poIn!=pr".asFormula,
        s"ep>0 & D>=0 & S>=0 & abs(dIn-dIn0)<=D & abs(poIn-poIn0)<=S*$t & (sr>0 -> poIn!=pr)".asFormula)
      println("Ctr1: " + ctr1.contract())
      println("Ctr2: " + ctr2.contract())

      if (ctr1.verifyBaseCase(QE).isEmpty)
        println(c1.name + " contract baseCase NOT verified!")
      else
        println(c1.name + " contract baseCase verified!")
      if (ctr1.verifyUseCase(QE).isEmpty)
        println(c1.name + " contract useCase NOT verified!")
      else
        println(c1.name + " contract useCase verified!")
      if (ctr1.verifyStep(master()).isEmpty)
        println(c1.name + " contract step NOT verified!")
      else
        println(c1.name + " contract step verified!")
      println("Ctr1 verified? " + ctr1.isVerified())

      if (ctr2.verifyBaseCase(QE).isEmpty)
        println(c2.name + " contract baseCase NOT verified!")
      else
        println(c2.name + " contract baseCase verified!")
      if (ctr2.verifyUseCase(QE).isEmpty)
        println(c2.name + " contract useCase NOT verified!")
      else
        println(c2.name + " contract useCase verified!")
      if (ctr2.verifyStep(master()).isEmpty)
        println(c2.name + " contract step NOT verified!")
      else
        println(c2.name + " contract step verified!")

      println("Ctr2 verified? " + ctr2.isVerified())

      require(ctr1.isVerified(), "ctr1 must be verified!")
      require(ctr1.isVerified(), "ctr2 must be verified!")

      Contract.save(ctr1, name + "-1.cbcps")
      Contract.save(ctr2, name + "-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load(name + "-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load(name + "-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side1-" + v))
        require(Utility.loadLemma(name + "-side1-" + v).nonEmpty, "could not verify sideCondition " + f)
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-side2-" + v))
        require(Utility.loadLemma(name + "-side2-" + v).nonEmpty, "could not verify sideCondition " + f)
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Seq[Variable], Lemma] = mutable.Map[Seq[Variable], Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      Seq(v: _*) -> Utility.loadLemma(name + "-side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap[Seq[Variable], Seq[Variable]](
      Seq("dIn".asVariable) -> Seq("d".asVariable),
      Seq("poIn".asVariable) -> Seq("po".asVariable)
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name + "-cpo-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma] = mutable.Map[(Seq[Variable], Seq[Variable]), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name + "-cpo-" + v).get
    }
    }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())

    return ctr3.isVerified()
  }


  def tacticTest() = {
    val t = ((composeb('R) *) & (((assignb('R) & print("assigned")) | (testb('R) & print("tested") & useAt(DerivedAxioms.trueImplies, PosInExpr(0 :: Nil))('R))) *))
    //    println("proved? " + TactixLibrary.proveBy("[a:=5;b:=2;?true;c:=d;?true;]true".asFormula, t & closeT).isProved)
    //    println("proved? " + TactixLibrary.proveBy("[a:=5;b:=2;]true".asFormula, t & closeT).isProved)
    //    println("proved? " + TactixLibrary.proveBy("[c:=d;]true".asFormula, t & closeT).isProved)
    //    println("proved? " + TactixLibrary.proveBy("[?true;c:=d;?true;]true".asFormula, t & closeT).isProved)
    //    println("proved? " + TactixLibrary.proveBy("[?true;?true;]true".asFormula, t & closeT).isProved)
    //    println("proved? " + TactixLibrary.proveBy("[?true;]true".asFormula, t & closeT).isProved)

    //    println("proved? " + TactixLibrary.proveBy("[{{{{r0:=r;a_0:=a_;}i1i10:=i1i1;}r_0:=r_;}a_0:=a;}i2o20:=i2o2;](r0=r_0&true)".asFormula,
    //      composeb('R) & assignb('R) ).isProved)
    println("proved? " + TactixLibrary.proveBy("[{{{{r0:=r;a_0:=a_;}i1i10:=i1i1;}r_0:=r_;}a_0:=a;}i2o20:=i2o2;](r0=r_0&true)".asFormula, t & closeT).isProved)

  }

  def posTest(): Unit = {
    val f = "[?a>0;][b:=c;][a:=42;]true".asFormula
    println("pos: " + Contract.ComposeProofStuff.posOfAssign(f.asInstanceOf[Box], "a".asVariable))
  }

  def inTest() = {
    val i = Interface.SinglePortInterface(mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "b".asVariable -> "b>0".asFormula, "c".asVariable -> "c>0".asFormula, "d".asVariable -> "d>0".asFormula), mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap.empty[Variable, Variable])
    println("i.in=" + i.in)

    TactixLibrary.proveBy(Imply("d>0".asFormula, Box(i.in, "d>0".asFormula)), implyR('R) & composeb('R) * (countBinary[Compose](i.in.asInstanceOf[Compose]) / 2) & print("a"))
  }

  def countBinary[C <: BinaryComposite](c: C): Integer = c match {
    case Compose(c1: C, c2: C) => countBinary(c1) + countBinary(c2) + 1
    case Compose(c1: C, _) => countBinary(c1) + 1
    case Compose(_, c2: C) => countBinary(c2) + 1
    case Compose(_, _) => 1
  }

  def piOutAllTest() = {
    val i = Interface.SinglePortInterface(mutable.LinkedHashMap.empty[Variable, Formula], mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "b".asVariable -> "b>0".asFormula, "c".asVariable -> "c>0".asFormula, "d".asVariable -> "d>0".asFormula), mutable.LinkedHashMap.empty[Variable, Variable])
    println("i.piOutAll=" + i.piOutAll)

    TactixLibrary.proveBy(Imply("d>0&c>0&b>0".asFormula, i.piOutAll), implyR('R) & (andL('L) *) & (andR('R) & print("x") < (skip, closeId) & print("y")) * 2)
  }

  def dci() = {
    val f = "[{c&H(||)}]p(||) -> [{c&H(||)&r(||)}]p(||)".asFormula
    //    val t = implyR('R) & useAt("DC differential cut", PosInExpr(1 :: 1 :: Nil))('R) < (
    val t = implyR('R) & useAt(DerivedAxioms.DWeakening, PosInExpr(0 :: Nil))('R) &
      useAt(DerivedAxioms.DWeakening, PosInExpr(0 :: Nil))('L) &
      useAt("DC differential cut", PosInExpr(1 :: 1 :: Nil))('R) &
      (print("x") partial)
    TactixLibrary.proveBy(f, t)
  }

  def diffTest() = {
    val f = "[{a'=1,b'=2&a<100&b<100}]a>42".asFormula
    f match {
      case Box(o: ODESystem, f: Formula) =>

        var leftmost: DifferentialProgram = o.ode
        var search = true
        while (search) {
          leftmost match {
            case s: AtomicODE => search = false
            case p: DifferentialProduct => leftmost = p.left
          }
        }
        println("leftmost dg? " + leftmost)
    }
  }

  def verifyContract1(ctr1: Contract): Boolean = {
    println(ctr1.component.name + " - Base Case: " + (ctr1.verifyBaseCase(QE) match {
      case None => "NOT verified."
      case Some(p) => "verified." + " -> LemmaID='" + ctr1.baseCaseLemma.get.name.get + "'"

    }));
    println(ctr1.component.name + " - Use Case: " + (ctr1.verifyUseCase(QE) match {
      case None => "NOT verified."
      case Some(p) => "verified." + " -> LemmaID='" + ctr1.useCaseLemma.get.name.get + "'"
    }));
    println(ctr1.component.name + " - Step: " + (ctr1.verifyStep(
      implyR('R) & (composeb('R) *) & testb('R)
        & implyR('R) & assignb('R) & assignb('R) & solve('R)
        & implyR('R) & composeb('R) & randomb('R) & allR('R) & testb('R) & implyR('R) & testb('R) & implyR('R)
        & QE
    ) match {
      case None => "NOT verified."
      case Some(p) => "verified." + " -> LemmaID='" + ctr1.stepLemma.get.name.get + "'"
    }));

    ctr1.isVerified()
  }

  def verifyContract2(ctr2: Contract): Boolean = {
    println(ctr2.component.name + " - Base Case: " + (ctr2.verifyBaseCase(QE) match {
      case None => "NOT verified."
      case Some(p) => "verified." + " -> LemmaID='" + ctr2.baseCaseLemma.get.name.get + "'"
    }));
    println(ctr2.component.name + " - Use Case: " + (ctr2.verifyUseCase(QE) match {
      case None => "NOT verified."
      case Some(p) => "verified." + " -> LemmaID='" + ctr2.useCaseLemma.get.name.get + "'"
    }));
    println(ctr2.component.name + " - Step: " + (ctr2.verifyStep(
      implyR('R) & (composeb('R) *) & testb('R)
        & implyR('R) & choiceb('R) & andR('R) < (
        assignb('R) & assignb('R) & solve('R) & implyR('R) & composeb('R) & randomb('R) & allR('R) & testb('R) & implyR('R) & testb('R) & implyR('R) & QE,
        assignb('R) & assignb('R) & solve('R) & implyR('R) & composeb('R) & randomb('R) & allR('R) & testb('R) & implyR('R) & testb('R) & implyR('R) & QE
      )
    ) match {
      case None => "NOT verified."
      case Some(p) => "verified." + " -> LemmaID='" + ctr2.stepLemma.get.name.get + "'"
    }));

    ctr2.isVerified()
  }

  def verifyContract1Lemma(ctr1: Contract): Boolean = {
    ctr1.verifyBaseCase("C1-BaseCase")
    ctr1.verifyUseCase("C1-UseCase")
    ctr1.verifyStep("C1-Step")

    ctr1.isVerified()
  }

  def verifyContract2Lemma(ctr2: Contract): Boolean = {
    ctr2.verifyBaseCase("C2-BaseCase")
    ctr2.verifyUseCase("C2-UseCase")
    ctr2.verifyStep("C2-Step")

    ctr2.isVerified()
  }

  def lemmaTest() = {
    val f = "a>0-> (a>-1 & a>-2)".asFormula
    val p = TactixLibrary.proveBy(f, QE)
    val l = Utility.addLemma("lemmaTest", p)

    val f2 = "a>0-> (a>-2 & a>-1)".asFormula
    val p2 = TactixLibrary.proveBy(f2, by(l))
    println("p2? " + p2.isProved)
  }

  def prettyPrinterTest() = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val a = "a=0".asFormula
    val b = "b=1".asFormula
    val c = "c=2".asFormula
    println(And(And(a, b), c))

    PrettyPrinter.setPrinter(FullPrettyPrinter)
    println(And(And(a, b), c))
  }

  def matchTest(s: String): Unit = {
    matchTest(s.split(",").toList)
  }

  def matchTest(s: List[String]): Unit = {
    s match {
      case v :: p :: tail =>
        println("v=" + v + ", p=" + p)
        matchTest(tail)
      case _ => println("NO MATCH")
    }
  }


  def variableTest(prog: Program = "{{y:=x;{a:=a+y;};{{{x:=1;}++{x:=3;}}}}++{{{{x:=1;}++{x:=3;}}};y:=x;{a:=a+y;}}}".asProgram) = {
    println("fv: " + StaticSemantics(prog).fv)
    println("bv: " + StaticSemantics(prog).bv)
    println("mbv: " + StaticSemantics(prog).mbv)

  }

  def proofTest(f: Formula, t: BelleExpr): Unit = proofTest(Sequent(immutable.IndexedSeq.empty[Formula], immutable.IndexedSeq(f)), t)

  def proofTest(s: Sequent, t: BelleExpr) = {
    val ret = TactixLibrary.proveBy(s, t)
    println("ret: " + ret)
  }

  def differentialProgramTest() = {
    var plant: Program = "{t'=1&true}".asProgram
    println("" + plant.isInstanceOf[DifferentialProgram])
  }

  def positionTest() = {
    val ret = TactixLibrary.proveBy(Sequent(immutable.IndexedSeq.empty, immutable.IndexedSeq("[?true;a:=2;?true;]a=2".asFormula)),
      master())
  }
}

//*@ TheType()


/*

object ComponentTester {
  def main(args: Array[String]) {
    val c1: Component = new Component
    c1.ctrl = "a:=a+y;".asProgram
    //    c1.plant = ODESystem("a'=0".asProgram.asInstanceOf[DifferentialProgram])
    c1.plant = "a'=0".asProgram.asInstanceOf[ODESystem]
    c1.pre = "a=0".asFormula
    c1.post = "a>=0".asFormula
    c1.vGlobal = Set()
    c1.vIn = Set("y".asVariable)
    //    c1.vOut = Set("out1")
    c1.vLocal = Set("a".asVariable)
    c1.piIn = Map("y".asVariable -> "y>=0".asFormula)
    //    c1.piOut = Map("out1" -> "out1=42")
    c1.name = "C1"

    val c2: Component = new Component
    c2.ctrl = "{{x:=1;}++{x:=3;}}".asProgram
    c2.plant = "x'=1&x<=2".asProgram.asInstanceOf[ODESystem]
    c2.pre = "x=2".asFormula
    c2.post = "true".asFormula
    c2.vGlobal = Set()
    //    c2.vIn = Set("in2")
    c2.vOut = Set("x".asVariable)
    c2.vLocal = Set()
    c2.piOut = Map("x".asVariable -> "x>=1".asFormula)
    //    c2.piIn = Map("in2" -> "in2=42")
    c2.name = "C2"

    ProofHelper.initProver


    println("---C1---")
    println("valid? " + c1.isValid())
    println("CTR: " + c1.contract)
    //    c1.verifyContract(ComponentProof.getTactic(ls(implyR) & la(andL), "a>=0".asFormula, debug("Base Case") & QE, debug("Use Case") & QE, debug("Step") & ls(implyR) & ls(composeb) & ls(randomb) & ls(allR) & ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(assignb) & ls(diffSolve) & QE))
    val cp1: ComponentProof = ComponentProof("a>=0".asFormula)
    val pg1 = c1.proofGoals(cp1.invariant)
    pg1.foreach(x => x match {
      case (n: String, s: Sequent) if (n == indInitLbl) => cp1.indInit = ProofHelper.verify(s, debug("<< C1 INIT >>") & QE, "C1-init").getOrElse(null)
      case (n: String, s: Sequent) if (n == indUseCaseLbl) => cp1.indUseCase = ProofHelper.verify(s, debug("<< C1 USECASE >>") & QE, "C1-usecase").getOrElse(null)
      case (n: String, s: Sequent) if (n == indStepLbl) => cp1.indStep = ProofHelper.verify(s, debug("<< C1 STEP >>") & implyR(1) & composeb(1) & composeb(1) & composeb(1) & randomb(1) & allR(1) & testb(1) & implyR(1) & assignb(1) & diffSolve(1) & QE, "C1-step").getOrElse(null)
      case (n: String, _) => require(false, "Unexpected proof goal '" + n + "'!")
    })
    println("cp1 isComplete? " + cp1.isComplete)
    c1.verifyContractBy(cp1, true)
    println("verified? " + c1.isVerified)

    println("---C2---")
    println("valid? " + c2.isValid)
    println("CTR: " + c2.contract)
    //    c2.verifyContract(ComponentProof.getTactic(ls(implyR) & la(andL), "x<=3&x>=1".asFormula, debug("Base Case") & QE, debug("Use Case") & QE, debug("Step") & ls(implyR) & ls(composeb) & ls(choiceb) & ls(andR) &&(ls(assignb) & ls(diffSolve) & QE, ls(assignb) & ls(diffSolve) & QE)))
    val cp2: ComponentProof = ComponentProof("x<=3&x>=1".asFormula)
    val pg2 = c2.proofGoals(cp2.invariant)
    pg2.foreach(x => x match {
      case (n: String, s: Sequent) if (n == indInitLbl) => cp2.indInit = ProofHelper.verify(s, debug("<< C2 INIT >>") & QE, "C2-init").getOrElse(null)
      case (n: String, s: Sequent) if (n == indUseCaseLbl) => cp2.indUseCase = ProofHelper.verify(s, debug("<< C2 USECASE >>") & QE, "C2-usecase").getOrElse(null)
      case (n: String, s: Sequent) if (n == indStepLbl) => cp2.indStep = ProofHelper.verify(s, debug("<< C2 STEP >>") & ls(implyR) & ls(composeb) & ls(composeb) & ls(testb) & ls(implyR) & ls(choiceb) & ls(andR) && (ls(assignb) & ls(diffSolve) & QE, ls(assignb) & ls(diffSolve) & QE), "C2-step").getOrElse(null)
    })
    println("cp2 isComplete? " + cp2.isComplete)
    c2.verifyContractBy(cp2, true)
    println("verified? " + c2.isVerified)

    val X = Map(
      "y".asVariable -> "x".asVariable
      //      ,"in2" -> "out1"
    )
    val c3 = Component.compose(c1, c2, X)
    println("c3: " + c3)

    println("c3 valid? " + c3.isValid)


    val f = Component.compatibilityProofObligation(c1, c2, X)
    println("c1 and c2 CPO: " + f.getOrElse("invalid"))
    val cpoLemma = ProofHelper.verify(f.getOrElse("false".asFormula), assignb(1) & implyR(1) & QE, "CPO")
    println("CPO proved? " + cpoLemma.isDefined)

    if (cpoLemma.isDefined) {
      val lemma3 = Component.verifyComposite(c1, c2, X, cpoLemma.get)
      if (lemma3.isDefined) println("c3 proved? " + lemma3.get.fact.isProved)
      else println("c3 proof failed!")
    }

    ProofHelper.shutdownProver

  }*/
