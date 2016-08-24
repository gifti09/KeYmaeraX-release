package cbcps

import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core.{And, NamedSymbol, StaticSemantics, SuccPos, _}
import edu.cmu.cs.ls.keymaerax.launcher.{DefaultConfiguration, LemmaDatabaseInitializer}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool, ToolEvidence}
import edu.cmu.cs.ls.keymaerax.tools._
import Utility._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import sun.security.provider.certpath.IndexedCollectionCertStore

import scala.collection.immutable._
import scala.collection.immutable.Nil
import scala.util.Try


object Utility {

  def v(f: Expression): Set[Variable] =
    StaticSemantics.vars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def fv(f: Expression): Set[Variable] =
    StaticSemantics.freeVars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def bv(f: Formula): Set[Variable] =
    StaticSemantics.boundVars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def bv(f: Program): Set[Variable] =
    StaticSemantics.boundVars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def loadLemma(id: LemmaID): Option[Lemma] = LemmaDBFactory.lemmaDB.get(id)

  def addLemma(lemmaName: String, fact: Provable): Lemma = {
    require(fact.isProved, "only proved Provables would be accepted as lemmas: " + lemmaName + " got\n" + fact)
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(Map("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemma = Lemma(fact, evidence, Some(lemmaName))
    // first check whether the lemma DB already contains identical lemma name
    val lemmaID = if (LemmaDBFactory.lemmaDB.contains(lemmaName)) {
      // identical lemma contents with identical name, so reuse ID
      if (LemmaDBFactory.lemmaDB.get(lemmaName).contains(lemma)) lemma.name.get
      else throw new IllegalStateException("Prover already has a different lemma filed under the same name " + LemmaDBFactory.lemmaDB.get(lemmaName) + " (stored in file name " + lemmaName + ") instnead of " + lemma)
    } else {
      LemmaDBFactory.lemmaDB.add(lemma)
    }
    LemmaDBFactory.lemmaDB.get(lemmaID).get
  }

  def containsLemma(lemmaName: String): Boolean = LemmaDBFactory.lemmaDB.contains(lemmaName)
}

object ProofHelper {
  def initProver = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerate[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p -> inv))
    TactixLibrary.invGenerator = generator

    val mathematica = new Mathematica()
    mathematica.init(DefaultConfiguration.defaultMathematicaConfig)
    DerivedAxioms.qeTool = mathematica
    TactixLibrary.tool = mathematica
  }

  def shutdownProver = {
    if (DerivedAxioms.qeTool != null) {
      DerivedAxioms.qeTool match {
        case t: Tool => t.shutdown()
      }
      DerivedAxioms.qeTool = null
    }
    if (TactixLibrary.tool != null) {
      TactixLibrary.tool match {
        case t: Tool => t.shutdown()
      }
      TactixLibrary.tool = null
      TactixLibrary.invGenerator = new NoneGenerate()
    }
  }

  def verify(goal: Sequent, t: BelleExpr, baseName: Option[String] = None): Option[Lemma] = {
    val p = TactixLibrary.proveBy(goal, t)
    if (p.isProved) {
      if (baseName.isEmpty) {
        Some(null)
      } else {
        val lemmaName = baseName.get
        val t = Try(addLemma(lemmaName, p))
        if (t.isFailure) {
          var i = 1
          var newLemmaName = lemmaName + i
          while (containsLemma(newLemmaName)) {
            i += 1
            newLemmaName = lemmaName + i
          }
          Some(addLemma(newLemmaName, p))
        }
        else {
          Some(t.get)
        }
      }
    }
    else {
      None
    }
  }

  def verify(f: Formula, lemma: Lemma): Boolean = {
    val ret = TactixLibrary.proveBy(f, TactixLibrary.by(lemma))
    if (ret.isProved)
      return true
    else
      return false
  }

  def verify(f: Formula, tactic: BelleExpr): Boolean = verify(f, tactic, None) match {
    case None => false
    case Some(_) => true
  }

  def verify(f: Formula, tactic: BelleExpr, lemmaName: Option[String]): Option[Lemma] = {
    verify(Sequent(IndexedSeq.empty[Formula], IndexedSeq(f)), tactic, lemmaName)
  }

  def verify(s: Sequent, tactic: BelleExpr): Boolean = verify(s, tactic, None) match {
    case None => false
    case Some(_) => true
  }

  //  val helper = new ProvabilityTestHelper((x) => println(x))
  //  private val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
}


object Lemmas {

  ProofHelper.initProver

  //L1 BA - DONE
  val lemma1BA: DependentPositionTactic = "Lemma1" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(b, f)) => V(pos)
  })

  val f1ba = "[?a<0;a:=b;]a>=0->[?b=-1;][?a<0;a:=b;]a>=0".asFormula
  val n1ba = "Proof of Lemma1 - Drop Control BA"
  val t1ba = implyR('R) & lemma1BA('R) & prop

  //L1 AB - DONE
  val lemma1AB: DependentPositionTactic = "Lemma1" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(b, f)) => monb & V(pos)
  })

  val f1ab = "[?a<0;a:=b;]a>=0->[?a<0;a:=b;][?b=-1;]a>=0".asFormula
  val n1ab = "Proof of Lemma1 - Drop Control AB"
  val t1ab = implyR('R) & lemma1AB('R) & prop

  //L2 - TODO!
  def lemma2(pos: Integer, rotate: Integer, remove: Integer, commuteEvo: Boolean): DependentPositionTactic = "Lemma2" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(b, f)) => {
      var t: BelleExpr = useAt("DG++ System", PosInExpr(1 :: Nil))(pos) & useAt(", commute", PosInExpr(1 :: Nil))(pos) * (1 + rotate)
      if (commuteEvo) t = useAt(DerivedAxioms.domainCommute)(pos) & t
      t = t & (introduceForAllFromDG(pos) & useAt("DGi inverse differential ghost", PosInExpr(1 :: Nil))(pos)) * remove
      if (rotate == 0) t = t & useAt(", commute", PosInExpr(1 :: Nil))(pos)
      t
    }
  })

  val introduceForAllFromDG: DependentPositionTactic = "Introduce For-All from DG" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(b, f)) => {
      val v = nextVariable(sequent.succ(pos.top.getPos - 1))
      cut(Forall(Seq(v), sequent.succ(pos.top.getPos - 1))) < (
        allL(v, v)(SeqPos(sequent.ante.length - 1)) & prop, hide(pos))
    }
  })

  private def nextVariable(f: Formula): Variable = {
    f match {
      case Box(ODESystem(ode, _), _) => ode match {
        case AtomicODE(s, _) => println("a: " + s.x);
          s.x
        case DifferentialProduct(a: AtomicODE, _) => println("d: " + a.xp.x);
          a.xp.x
      }
    }
  }

  val f2 = "[{t'=1,x1'=c1(x1,x2,x3,T),x2'=c2(x1,x2,x3,T),x3'=c3(x1,x2,x3,T)&H1(x1,x2,x3,T)}]A(x1,x2,x3,T)->[{t'=1,x1'=c1(x1,x2,x3,T),x2'=c2(x1,x2,x3,T),x3'=c3(x1,x2,x3,T),y1'=d1(y1,y2,y3,y4,T),y2'=d2(y1,y2,y3,y4,T),y3'=d3(y1,y2,y3,y4,T),y4'=d4(y1,y2,y3,y4,T)&H1(x1,x2,x3,T)&G1(y1,y2,y3,y4,T)}]A(x1,x2,x3,T)".asFormula
  val n2 = "Proof of Lemma2 - Drop Plant"
  val t2 = implyR('R) & lemma2(1, 3, 4, false) & prop
  //  lazy val lemma2: Lemma = lemma(f2, n2, t2)
  //  lazy val lemma2T = TactixLibrary.byUS(lemma2)

  //L3 - DONE
  lazy val f3 = "([x:=*;]A(x))->([x:=p(x);]A(x))".asFormula
  lazy val n3 = "Proof of Lemma3 - Overapproximate Assignment"
  lazy val t3 = implyR('R) & assignb('R) & randomb('L) & allL("x".asVariable, "p(x)".asTerm)('L) & close(-1, 1)
  lazy val lemma3: Lemma = lemma(f3, n3, t3)
  lazy val lemma3T = TactixLibrary.byUS(lemma3)

  //Alternative: ls(implyR) & useAt(assignbEquationalAxiom)(1) & useAt(allSubstitute)(1) & la(randomb) & la(allL("x".asVariable, "p".asTerm)) & close(-1, 1)


  //L4 - TODO!
  val f4_1 = "[x:=a; y:=b;]A(a,b,x,y) <-> [y:=b; x:=a;]A(a,b,x,y)".asFormula
  val n4_1 = "Proof of Lemma4 - Reorder Programs 1"
  val t4_1 = equivR(1) < (
    // ->
    composeb('R) & composeb('L) & print("xx") & assignb('R) * 2 & assignb('L) * 2 & prop,
    // <-
    composeb('R) & composeb('L) & assignb('R) & assignb('R) & assignb('L) & assignb('L) & prop
    )
  lazy val lemma4_1: Lemma = lemma(f4_1, n4_1, t4_1)
  lazy val lemma4_1T = TactixLibrary.byUS(lemma4_1)
  val f4_2 = "[x:=*; y:=*;]A(x,y) <-> [y:=*; x:=*;]A(x,y)".asFormula
  val n4_2 = "Proof of Lemma4 - Reorder Programs 2"
  val t4_2 = equivR(1) < (
    // ->
    composeb('R) & composeb('L) & (randomb('R) & allR('R)) * 2 & randomb('L) & allL("x".asVariable)('L) & randomb('L) & allL("y".asVariable)('L) & prop,
    // <-
    composeb('R) & composeb('L) & (randomb('R) & allR('R)) * 2 & randomb('L) & allL("y".asVariable)('L) & randomb('L) & allL("x".asVariable)('L) & prop
    )
  lazy val lemma4_2: Lemma = lemma(f4_2, n4_2, t4_2)
  lazy val lemma4_2T = TactixLibrary.byUS(lemma4_2)
  val f4_3 = "[x:=*; y:=b;]A(b,x,y) <-> [y:=b; x:=*;]A(b,x,y)".asFormula
  val n4_3 = "Proof of Lemma4 - Reorder Programs 3"
  val t4_3 = equivR(1) < (
    // ->
    composeb('R) & composeb('L) & assignb('R) & randomb('R) & allR('R) & randomb('L) & allL("x".asVariable)('L) & assignb('L) & prop,
    // <-
    composeb('R) & composeb('L) & randomb('R) & allR('R) & assignb('R) & assignb('L) & randomb('L) & allL("x".asVariable)('L) & prop
    )
  lazy val lemma4_3: Lemma = lemma(f4_3, n4_3, t4_3)
  lazy val lemma4_3T = TactixLibrary.byUS(lemma4_3)
  val f4_4 = "[x:=*; ?B(a);]A(a,b,x,y) <-> [?B(a); x:=*;]A(a,b,x,y)".asFormula
  val n4_4 = "Proof of Lemma4 - Reorder Programs 4"
  val t4_4 = equivR(1) < (
    // ->
    composeb('R) & composeb('L) & testb('R) & randomb(1, 1 :: Nil) & testb(-1, 1 :: Nil) & randomb('L) & implyR('R) & allR('R) & allL("x".asVariable)('L) & implyL('L) & prop,
    // <-
    composeb('R) & composeb('L) & randomb('R) & allR('R) & randomb(-1, 1 :: Nil) & allL("x".asVariable)(-1, 1 :: Nil) & close(-1, 1)
    )
  lazy val lemma4_4: Lemma = lemma(f4_4, n4_4, t4_4)
  lazy val lemma4_4T = TactixLibrary.byUS(lemma4_4)
  val f4_5 = "[x:=a; ?B(a);]A(a,b,x,y) <-> [?B(a); x:=a;]A(a,b,x,y)".asFormula
  val n4_5 = "Proof of Lemma4 - Reorder Programs 5"
  val t4_5 = equivR(1) < (
    // ->
    composeb('R) & composeb('L) & assignb('L) & assignb(1, 1 :: Nil) & prop,
    // <-
    composeb('R) & composeb('L) & assignb('R) & assignb(-1, 1 :: Nil) & prop
    )
  lazy val lemma4_5: Lemma = lemma(f4_5, n4_5, t4_5)
  lazy val lemma4_5T = TactixLibrary.byUS(lemma4_5)
  val f4_6 = "[?F(a,b,x,y); ?G(a,b,x,y);]A(a,b,x,y) <-> [?G(a,b,x,y); ?F(a,b,x,y);]A(a,b,x,y)".asFormula
  val n4_6 = "Proof of Lemma4 - Reorder Programs 6"
  val t4_6 = equivR(1) < (
    // ->
    composeb('R) & composeb('L) & testb('R) & testb(1, 1 :: Nil) & testb('L) & testb(-1, 1 :: Nil) & prop,
    // <-
    composeb('R) & composeb('L) & testb('R) & testb(1, 1 :: Nil) & testb('L) & testb(-1, 1 :: Nil) & prop
    )
  lazy val lemma4_6: Lemma = lemma(f4_6, n4_6, t4_6)
  lazy val lemma4_6T = TactixLibrary.byUS(lemma4_6)

  /*
    val f5 = "[a();]F(??)->([a();?F();]A() <-> [a();]A())".asFormula
    val n5 = "Proof of Lemma5 - Introduce Test"
    val t5 = ls(implyR) & cut("([a;?F(??);]A(??) -> [a;]A(??)) & ([a;?F(??);]A(??) <- [a;]A(??))".asFormula) & onBranch(
      (cutUseLbl, la(andL) & ls(equivR) & onBranch(
        (equivLeftLbl, la(implyL) && (close(-3, 2), close(-4, 1))),
        (equivRightLbl, la(implyL) && (la(implyL) && (close(-2, 3), close(-3, 1)), la(implyL) && (close(-2, 2), close(-4, 1))))
      )),
      (cutShowLbl, ls(andR) && (hideR(1) & composeb(1, List(0)) & ls(K) & Monb & ls(implyR) & la(testb) & la(implyL) && (close(-1, 2), close(-2, 1)), hideR(1) & composeb(1, List(1)) & ls(K) & Monb & ls(implyR) & ls(testb) & ls(implyR) & close(-2, 1)))
    )


        val f6 = "(([?G(??);]A(??)) & (F(??)->G(??))) -> [?F(??);]A(??)".asFormula
        val n6 = "Proof of Lemma6 - Weaken Test"
        val t6 = ls(implyR) & la(andL) & la(testb) & ls(testb) & ls(implyR) & PropositionalTacticsImpl.modusPonensT(AntePosition(2), AntePosition(1)) & PropositionalTacticsImpl.modusPonensT(AntePosition(1), AntePosition(0)) & close

        //Corollary 1
        val f7 = "(([a;][?G(??);]A(??)) & [a;](F(??)->G(??))) ->[a;][?F(??);]A(??)".asFormula
        val n7 = "Proof of Corollary1- Weaken Test Context"
        val t7 = implyR(1) & useAt("[] split", PosInExpr(1 :: Nil))(-1) & Monb & PropositionalTacticsImpl.InverseImplyRightT() & useAt(lemma("Proof of Lemma6 - Weaken Test").get, PosInExpr())(1)
      */

  //  def lemma(n: String): Option[Lemma] = {
  //    val lemmaDB = LemmaDBFactory.lemmaDB
  //    lemmaDB.get(n)
  //  }

  def lemma(f: Formula, n: String, t: BelleExpr): Lemma = {
    //proved, so create lemma
    val lemmaDB = LemmaDBFactory.lemmaDB
    if (lemmaDB.contains(n)) return lemmaDB.get(n).get
    else {
      val proof = TactixLibrary.proveBy(f, t)
      if (proof.isProved) {
        val evidence = ToolEvidence(Map("input" -> proof.toString, "output" -> "true")) :: Nil
        val l = Lemma(proof, evidence, Some(n))
        val lemmaID = if (lemmaDB.contains(n)) {
          // identical lemma contents with identical name, so reuse ID
          if (lemmaDB.get(n).contains(l)) l.name.get
          else throw new IllegalStateException("Prover already has a different lemma filed under the same name '" + n + "'")
        } else {
          lemmaDB.add(l)
        }
        return lemmaDB.get(lemmaID).get
      }
      else
        null
    }
  }

  /*
    def proofAll = {
      //Lemma 3
      if (null == lemma(f3, n3, t3))
        println("Error proving '" + n3 + "'!")
      else
        println("Verified " + n3)

      //Lemma 4
      if (null == lemma(f4, n4, t4))
        println("Error proving '" + n4 + "'!")
      else
        println("Verified " + n4)

      //Lemma 5 - closes!
      if (null == lemma(f5, n5, t5))
        println(" Error proving '" + n5 + "'!")
      else
        println("Verified " + n5)

      //Lemma 6
      if (null == lemma(f6, n6, t6))
        println("Error proving '" + n6 + "'!")
      else
        println("Verified " + n6)

      //Corollary 1
      if (null == lemma(f7, n7, t7))
        println("Error proving '" + n7 + "'!")
      else
        println("Verified " + n7)
    }
  */

  //  def lemma1BA(pos: Integer): Tactic = HybridProgramTacticsImpl.boxVacuousT(pos) & prop
  //  def lemma1AB(pos: Integer): Tactic = AxiomaticRuleTactics.boxMonotoneT & HybridProgramTacticsImpl.boxVacuousT(pos) & prop


  def main(args: Array[String]) {
    //        proofAll

    //    println("Test Lemma 3 - proved? " + TactixLibrary.proveBy("[a:=4;?a>0;]a>0".asFormula, composeb('R) & useAt(lemma3, PosInExpr(1 :: Nil))('R) & print("x")).isProved)
    //    println("Test Lemma 4_1 - proved? " + TactixLibrary.proveBy("[a:=a1;b:=b1;]a>0 -> [b:=b1;a:=a1;](a>0&b>0&a1>0&b1>0)".asFormula, implyR('R) & useAt(lemma4_1, PosInExpr(0 :: Nil))('R) & print("x")).isProved)
        println("Test Lemma 4_2 - proved? " + TactixLibrary.proveBy("[a:=*;b:=*;]a>0 -> [b:=*;a:=*;]a>0".asFormula, implyR('R) & useAt(lemma4_2, PosInExpr(0 :: Nil))('R) & print("x")).isProved)


//    TactixLibrary.proveBy("[c:=d;][a:=b;]A(??)->[a:=b;][c:=d;]A(??)".asFormula, assignb(1, 0 :: Nil) & assignb(1, 0 :: 0 :: 1 :: Nil) & assignb(1, 1 :: Nil) & assignb(1,1::0::1::Nil) & implyR(1)& print("x")  partial)
    return

    val f = f4_1
    val n = n4_1
    val t = t4_1
    if (null == lemma(f, n, t))
      println(" Error proving '" + n + "'!")
    else
      println("Verified " + n)
    ProofHelper.shutdownProver
  }
}
