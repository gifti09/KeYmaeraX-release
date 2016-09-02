package cbcps

import java.io.FileInputStream
import java.time.DayOfWeek

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PosInExpr}
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedAxioms, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{DifferentialProgram, ODESystem, Program}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXPrettyPrinter}
import testHelper.ParserFactory._

import scala.collection.mutable._
import scala.collection.immutable

/**
  * Created by Andreas on 19.11.2015.
  */
object Tester {


  def main(args: Array[String]) {

    ProofHelper.initProver

    //    test()


/*
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
*/

    val lc1 = Contract.load("contract1.cbcps")
    val lc2 = Contract.load("contract2.cbcps")
    println("Loaded Contract(C1,I1) verified? " + lc1.isVerified())
    println("Loaded Contract(C2,I2) verified? " + lc2.isVerified())

    val X = immutable.Map(
      "y".asVariable -> "x".asVariable
    )

    var cpoT: immutable.Map[(Variable, Variable), BelleExpr] = immutable.Map.empty
    cpoT += ("y".asVariable, "x".asVariable) -> (implyR('R) & assignb('R) & implyR('R) & QE)
    println("CPO verified? " + cpoT.forall { case (m, t) => TactixLibrary.proveBy(lc1.cpo(lc2, X)(m), t).isProved })

    val sc1T = master()
    val sc1 = TactixLibrary.proveBy(lc1.sideCondition(lc2, X), sc1T)
    println("SC1 verified? " + sc1.isProved)
    val sc2T = master()
    val sc2 = TactixLibrary.proveBy(lc2.sideCondition(lc1, X), sc2T)
    println("SC2 verified? " + sc2.isProved)

    println("Composing...")
    val ctr3 = Contract.compose(lc1, lc2, X, cpoT, sc1T, sc2T)
    println("Contract(C1,I1)=\n\t" + lc1.contract())
    println("Contract(C2,I2)=\n\t" + lc2.contract())
    println("Contract( (C1,I1)||(C2,I2) )=\n\t" + ctr3.contract())

    //    val lemmaDB = LemmaDBFactory.lemmaDB
    //    val cpoLemma = lemmaDB.get(new lemmaDB.LemmaID("CPO"))
    //
    //    if (cpoLemma.isDefined && ProofHelper.verify(Component.compatibilityProofObligation(c1, c2, X).getOrElse(False), cpoLemma.get).isDefined)
    //      Component.verifyComposite(c1, c2, X, cpoLemma.get)
    //    else
    //      println("CPO not defined!")

    ProofHelper.shutdownProver
  }

  // --- HELPER METHODS ---

  def test() = {
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
    dci()

    System.exit(0)
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
