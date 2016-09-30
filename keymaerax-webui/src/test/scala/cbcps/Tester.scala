package cbcps

import java.io.FileInputStream
import java.time.DayOfWeek

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PosInExpr}
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedAxioms, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{DifferentialProgram, ODESystem, Program}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXPrettyPrinter}
import testHelper.ParserFactory._

import scala.collection.immutable.{List, Map}
import scala.collection.mutable._
import scala.collection.{immutable, mutable}

/**
  * Created by Andreas on 19.11.2015.
  */
object Tester {


  def main(args: Array[String]) {
    test()
  }

  // --- HELPER METHODS ---

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

    //    test1()
    //    bigTest()
    test2(true)

    ProofHelper.shutdownProver
    System.exit(0)
  }

  def test1() = {
    //Component 1
    val c1: Component = {
      new Component("C1", //Name
        "a:=a+y;".asProgram, //Control
        "a'=0".asProgram.asInstanceOf[ODESystem]) //Plant
    }
    //Interface 1
    val i1: Interface = {
      new Interface(
        LinkedHashMap("y".asVariable -> "y>=0".asFormula), //In
        LinkedHashMap(//Out
          "out1".asVariable -> "out1=42".asFormula
        )
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
    Contract.save(ctr1, "contract1.cbcps")

    //Component 2
    val c2: Component = {
      new Component("C2", //Name
        "{{x:=1;}++{x:=3;}}".asProgram, //Control
        "x'=1&x<=2".asProgram.asInstanceOf[ODESystem]) //Plant
    }
    //Interface 2
    val i2: Interface = {
      new Interface(
        LinkedHashMap("in2".asVariable -> "in2=42".asFormula), //In
        LinkedHashMap(//Out
          "x".asVariable -> "x>=1".asFormula
          //                    ,"out2".asVariable -> "true".asFormula
        )
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
    Contract.save(ctr2, "contract2.cbcps")

    //Everything Verified?
    println("Contract(C1,I1) verified? " + ctr1.isVerified())
    println("Contract(C2,I2) verified? " + ctr2.isVerified())


    val lc1 = Contract.load("contract1.cbcps")
    val lc2 = Contract.load("contract2.cbcps")
    println("Contract(C1,I1) = " + lc1.contract())
    println("Loaded Contract(C1,I1) verified? " + lc1.isVerified())
    println("Contract(C2,I2) = " + lc2.contract())
    println("Loaded Contract(C2,I2) verified? " + lc2.isVerified())

    val X = mutable.LinkedHashMap(
      "y".asVariable -> "x".asVariable
    )

    var cpoT: mutable.Map[(Variable, Variable), BelleExpr] = mutable.Map.empty
    cpoT += ("y".asVariable, "x".asVariable) -> (implyR('R) & assignb('R) & implyR('R) & QE)
    //    println("CPO verified? " + cpoT.forall { case (m, t) => TactixLibrary.proveBy(lc1.cpo(lc2, X)(m), t).isProved })

    val sc1 = lc1.sideConditions()
    val sc1T: mutable.Map[Variable, BelleExpr] = sc1.map((e) => (e._1, master()))
    println("sc1: " + sc1)
    //    println("SC1 verified? " + TactixLibrary.proveBy(lc1.sideCondition(), sc1T).isProved)

    val sc2 = lc2.sideConditions()
    val sc2T: mutable.Map[Variable, BelleExpr] = sc2.map((e) => (e._1, master()))
    println("sc2: " + sc2)
    //    println("SC2 verified? " + TactixLibrary.proveBy(lc2.sideCondition(), sc2T).isProved)

    println("Composing...")
    val ctr3 = Contract.composeWithSideTactics(lc1, lc2, X, cpoT, sc1T, sc2T)
    println("Contract(C1,I1)=\n\t" + lc1.contract())
    println("Contract(C2,I2)=\n\t" + lc2.contract())
    println("Contract( (C1,I1)||(C2,I2) )=\n\t" + ctr3.contract())
    println("Contract (C3,I3) verified? " + ctr3.isVerified())

  }


  def test2(initialize: Boolean = true,name:String="test2") = {
    if (initialize) {
      val c1 = new Component(name+"-D1", "?x>0;a:=42;".asProgram, ODESystem("b'=1".asDifferentialProgram, "b<1".asFormula))
      val c2 = new Component(name+"-D2", "u:=-1;?y<42;".asProgram, ODESystem("v'=-1".asDifferentialProgram, "v>0".asFormula))
      val i1 = new Interface(mutable.LinkedHashMap.empty, mutable.LinkedHashMap("a".asVariable -> "a>5".asFormula, "b".asVariable -> "b<1".asFormula))
      val i2 = new Interface(mutable.LinkedHashMap("y".asVariable -> "y>0".asFormula))
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

      Contract.save(ctr1, "t2-1.cbcps")
      Contract.save(ctr2, "t2-2.cbcps")
      println("Saved both contracts!")
    }

    val lctr1 = Contract.load("t2-1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load("t2-2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name+"side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name+"side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side condition
    val sc1: mutable.Map[Variable, Lemma] = mutable.Map[Variable, Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name+"side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Variable, Lemma] = mutable.Map[Variable, Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name+"side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap(
      "y".asVariable -> "a".asVariable
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name+"cpo1-2-" + v))
      }
      }
      lctr2.cpo(lctr1, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some(name+"cpo2-1-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Variable, Variable), Lemma] = mutable.Map[(Variable, Variable), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma(name+"cpo1-2-" + v).get
    }
    }.toSeq: _*) ++
      mutable.Map[(Variable, Variable), Lemma](lctr2.cpo(lctr1, X).map { case (v, f: Formula) => {
        v -> Utility.loadLemma(name+"cpo2-1-" + v).get
      }
      }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())
  }

  def bigTest() = {
    val initialize = true
    if (initialize) {
      val c1 = new Component("B1", "?ctr1>0;".asProgram, ODESystem("p1'=1".asDifferentialProgram, "p1<1".asFormula))
      val c2 = new Component("B2", "?ctr2<42;".asProgram, ODESystem("p2'=1".asDifferentialProgram, "p2<1".asFormula))
      val i1 = new Interface(mutable.LinkedHashMap("r".asVariable -> "r>0".asFormula, "i1i1".asVariable -> "i1i1>0".asFormula, "s".asVariable -> "s>0".asFormula, "i1i2".asVariable -> "i1i2>0".asFormula), mutable.LinkedHashMap("a_".asVariable -> "a_>0".asFormula, "i1o1".asVariable -> "i1o1>0".asFormula, "b_".asVariable -> "b_>0".asFormula, "i1o2".asVariable -> "i1o2>0".asFormula))
      val i2 = new Interface(mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "i2i1".asVariable -> "i2i1>0".asFormula, "b".asVariable -> "b>0".asFormula, "i2i2".asVariable -> "i2i2>0".asFormula), mutable.LinkedHashMap("r_".asVariable -> "r_>0".asFormula, "i2o1".asVariable -> "i2o1>0".asFormula, "s_".asVariable -> "s_>0".asFormula, "i2o2".asVariable -> "i2o2>0".asFormula))
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

      Contract.save(ctr1, "big1.cbcps")
      Contract.save(ctr2, "big2.cbcps")
      println("Saved both contracts!")
    }
    val lctr1 = Contract.load("big1.cbcps")
    println("Loaded ctr2! verified? " + lctr1.isVerified())
    println("LCtr1: " + lctr1.contract())
    val lctr2 = Contract.load("big2.cbcps")
    println("Loaded ctr2! verified? " + lctr2.isVerified())
    println("LCtr2: " + lctr2.contract())

    if (initialize) {
      //Verify lemmas for side conditions
      lctr1.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some("side1-" + v))
      }
      }
      lctr2.sideConditions().foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some("side2-" + v))
      }
      }
    }
    //Reuse previously verified lemmas for side contision
    val sc1: mutable.Map[Variable, Lemma] = mutable.Map[Variable, Lemma](lctr1.sideConditions().map { case (v, f: Formula) => {
      v -> Utility.loadLemma("side1-" + v).get
    }
    }.toSeq: _*)
    val sc2: mutable.Map[Variable, Lemma] = mutable.Map[Variable, Lemma](lctr2.sideConditions().map { case (v, f: Formula) => {
      v -> Utility.loadLemma("side2-" + v).get
    }
    }.toSeq: _*)

    val X = mutable.LinkedHashMap(
      "r".asVariable -> "r_".asVariable,
      "s".asVariable -> "s_".asVariable,
      "a".asVariable -> "a_".asVariable,
      "b".asVariable -> "b_".asVariable
    )

    if (initialize) {
      //Verify lemmas for cpo
      lctr1.cpo(lctr2, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some("cpo1-2-" + v))
      }
      }
      lctr2.cpo(lctr1, X).foreach { case (v, f: Formula) => {
        v -> ProofHelper.verify(f, master(), Some("cpo2-1-" + v))
      }
      }
    }

    //Reuse previously verified lemmas for cpo
    val cpo: mutable.Map[(Variable, Variable), Lemma] = mutable.Map[(Variable, Variable), Lemma](lctr1.cpo(lctr2, X).map { case (v, f: Formula) => {
      v -> Utility.loadLemma("cpo1-2-" + v).get
    }
    }.toSeq: _*) ++
      mutable.Map[(Variable, Variable), Lemma](lctr2.cpo(lctr1, X).map { case (v, f: Formula) => {
        v -> Utility.loadLemma("cpo2-1-" + v).get
      }
      }.toSeq: _*)


    var ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, false)
    println("Ctr3: " + ctr3.contract())
    ctr3 = Contract.composeWithLemmas(lctr1, lctr2, X, cpo, sc1, sc2, true)
    println("Ctr3 verified? " + ctr3.isVerified())
  }

  def tacticTest() = {
    val t = (((composeb('R) | skip)
      & (assignb('R) | (testb('R) & useAt(DerivedAxioms.trueImplies, PosInExpr(0 :: Nil))('R)))) *)
    println("proved? " + TactixLibrary.proveBy("[a:=5;b:=2;?true;c:=d;?true;]true".asFormula, t & closeT).isProved)
    println("proved? " + TactixLibrary.proveBy("[a:=5;b:=2;]true".asFormula, t & closeT).isProved)
    println("proved? " + TactixLibrary.proveBy("[c:=d;]true".asFormula, t & closeT).isProved)
    println("proved? " + TactixLibrary.proveBy("[?true;c:=d;?true;]true".asFormula, t & closeT).isProved)
    println("proved? " + TactixLibrary.proveBy("[?true;?true;]true".asFormula, t & closeT).isProved)
    println("proved? " + TactixLibrary.proveBy("[?true;]true".asFormula, t & closeT).isProved)
  }

  def posTest(): Unit = {
    val f = "[?a>0;][b:=c;][a:=42;]true".asFormula
    println("pos: " + Contract.ComposeProofStuff.posOfAssign(f.asInstanceOf[Box], "a".asVariable))
  }

  def inTest() = {
    val i = new Interface(mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "b".asVariable -> "b>0".asFormula, "c".asVariable -> "c>0".asFormula, "d".asVariable -> "d>0".asFormula))
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
    val i = new Interface(mutable.LinkedHashMap.empty, mutable.LinkedHashMap("a".asVariable -> "a>0".asFormula, "b".asVariable -> "b>0".asFormula, "c".asVariable -> "c>0".asFormula, "d".asVariable -> "d>0".asFormula))
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
        & implyR('R) & assignb('R) & assignb('R) & diffSolve()('R)
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
        assignb('R) & assignb('R) & diffSolve()('R) & implyR('R) & composeb('R) & randomb('R) & allR('R) & testb('R) & implyR('R) & testb('R) & implyR('R) & QE,
        assignb('R) & assignb('R) & diffSolve()('R) & implyR('R) & composeb('R) & randomb('R) & allR('R) & testb('R) & implyR('R) & testb('R) & implyR('R) & QE
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
