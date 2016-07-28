package cbcps

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.LemmaID
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerate, DerivedAxioms, NoneGenerate, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.{Tool, ToolEvidence}


import scala.collection.immutable
import scala.collection.immutable._


/**
 * Created by Andreas on 22.10.2015.
 */


object cbcps {
  val usage: String = "cbps -name <String> (-ctrl <String> | -ctrlF <File>) (-plant <String> | -plantF <File>) " +
    "(-pre <String> | -preF <File>) (-pre <String> | -preF <File>) (-post <String> | -postF <File>) (-pre <String> | -preF <File>)" +
    "(-vIn <String> | -vInF <File>) (-vOut <String> | -vOutF <File>) (-vLocal <String> | -vLocalF <File>) (-vGlobal <String> | -vGlobalF <File>)"

  def main(args: Array[String]): Unit = {
    if (args.length == 0) println(usage)
    val arglist = args.toList

    var c: cbcpsold.Component = null
    c = cbcpsold.Component.parseComponent(c, arglist)
    if (c == null) {
      println(usage)
      sys.exit(1)
    }

    println(c)

    println("Hybrid Program for Input:")
    println(c.hp)

    println()
    println("Contract for Input:")
    println(c.contract)

    println()
    println("Component valid? " + c.isValid())

    //    println()
    //    println("Proof-Auto for Input:")
    //    var proof = c.verifyContract(TactixLibrary.master)
    //    println("closed? " + proof.isClosed() + ", proved? " + proof.isProved() + ", pretty provable: " + proof.provable.prettyString)
    //    println("Proof: \n" + proof)

    ProofHelper.initProver


    println()
    println("Proof-Manual for Input:")


    //gibt Provable, als lemma speichern, und an funktion uebergeben
    //TactixLibrary.proveBy("BaseCase".asFormula,master)

    //user beweist 3 lemmas, uebergibt die + invariante

    //    val lemma = c.verifyContract(ComponentProof.getTactic(ls(implyR) & la(andL), "(a>=0&b>10)".asFormula,
    //      debug("Base Case") & la(andL) & ls(andR) &&(QE, QE),
    //      debug("Use Case") & QE,
    //      debug("Step") & ls(implyR) & la(andL) & ls(composeb) & ls(randomb) & ls(allR) & ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(composeb) & ls(assignb) & ls(testb) & ls(implyR) & ls(diffSolve) & QE))
    //    if (lemma.isDefined && lemma.get.fact.isProved)
    //      println(">>> Proved!")
    //    else {
    //      println(">>> NOT Proved!")
    //      return
    //    }

    println("++++++++++++++++++++++++++++++++++++++++++++++++++")

    // use a lemma
    if (c.lemma.isDefined) {
      if (c.verifyContractBy(c.lemma.get, false))
        println("Proof by Lemma!")
      else
        println("Could not verify component with Lemma!!")
    }
    else
      println("Lemma was not verified!!")

    ProofHelper.shutdownProver
  }

}

/*
object ProofHelper {
  def initProver = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerate[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
  }

  def shutdownProver = {
    if (DerivedAxioms.qeTool != null) {
      DerivedAxioms.qeTool match { case t: Tool => t.shutdown() }
      DerivedAxioms.qeTool = null
    }
    if (TactixLibrary.tool != null) {
      TactixLibrary.tool match { case t: Tool => t.shutdown() }
      TactixLibrary.tool = null
      TactixLibrary.invGenerator = new NoneGenerate()
    }
  }

  def verify(f: Formula, lemma: Lemma): Option[Lemma] = {
    val ret = TactixLibrary.proveBy(f, TactixLibrary.by(lemma))
    if (ret.isProved)
      return Some(lemma)
    else
      return None
  }

  def verify(f: Formula, tactic: BelleExpr): Option[Lemma] = verify(f, tactic, null)

  def verify(f: Formula, tactic: BelleExpr, lemmaName: String): Option[Lemma] = {
    verify(Sequent(immutable.IndexedSeq[Formula](), immutable.IndexedSeq[Formula](f)), tactic, lemmaName)
  }

  def verify(s: Sequent, tactic: BelleExpr): Option[Lemma] = verify(s, tactic, null)

  def verify(s: Sequent, tactic: BelleExpr, name: String): Option[Lemma] = {
    val ret = TactixLibrary.proveBy(s, tactic)

    if (ret.isProved) {
      val lemmaName = if (name == null) "TempLemma" else name
      val evidence = ToolEvidence(Map("input" -> ret.toString, "output" -> "true")) :: Nil
      //proved, so keep lemma and save lemma to LemmaDB
      val lemmaDB = LemmaDBFactory.lemmaDB
      var i = 1
      var uniqueLemmaName = lemmaName
      while (lemmaDB.contains(new LemmaID(uniqueLemmaName))) {
        uniqueLemmaName = lemmaName + i
        i += 1
      }
      val l = Some(Lemma(ret, evidence, Some(uniqueLemmaName)))
      lemmaDB.add(l.get)
      return l
    }
    return None
  }

//  def invAndLT(p1: Position = AntePos(0), p2: Position = AntePos(1)): BelleExpr = new ConstructionTactic("invAndL") {
//
//    override def applicable(node: ProofNode): Boolean = isApplicable(node.sequent, p1, p2)
//
//    def isApplicable(s: Sequent, pos1: Position, pos2: Position): Boolean = pos1.isAnte && pos1.isTopLevel && pos1.isIndexDefined(s) &&
//      pos2.isAnte && pos2.isTopLevel && pos2.isIndexDefined(s) &&
//      pos1.index < pos2.index
//
//    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
//      val a1 = node.sequent.ante(p1.getIndex)
//      val a2 = node.sequent.ante(p2.getIndex)
//      val cutShowPos = SuccPos(node.sequent.succ.length)
//      import TactixLibrary.hide
//      Some(
//        PropositionalTacticsImpl.cutT(Some(And(a1, a2))) & onBranch(
//          (BranchLabels.cutShowLbl,
//            PropositionalTacticsImpl.AndRightT(cutShowPos) &&(
//              TacticLibrary.AxiomCloseT,
//              TacticLibrary.AxiomCloseT
//              )
//            ),
//          (BranchLabels.cutUseLbl, hide(a2)(p2) & hide(a1)(p1) /* This is the result. */ )
//        )
//      )
//
//    }
//  }
}


object Lemmas {

  ProofHelper.initProver

  val f1ba = "[?a<0;a:=b;]a>=0->[?b=-1;][?a<0;a:=b;]a>=0".asFormula
  val n1ba = "Proof of Lemma1 - Drop Control"
  val t1ba = implyR(1) & lemma1BA(1)

  def lemma1BA(pos: Integer): BelleExpr = new ConstructionTactic("Lemma1") {
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val t = HybridProgramTacticsImpl.boxVacuousT(pos)
      Some(t)
    }

    /** Returns true if this tactics is applicable to the proof node */
    override def applicable(node: ProofNode): Boolean = true
  }

  val f1ab = "[?a<0;a:=b;]a>=0->[?a<0;a:=b;][?b=-1;]a>=0".asFormula
  val n1ab = "Proof of Lemma1 - Drop Control"
  val t1ab = implyR(1) & lemma1AB(1)

  def lemma1AB(pos: Integer): BelleExpr = new ConstructionTactic("Lemma1") {
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      var t = AxiomaticRuleTactics.boxMonotoneT
      t = t & HybridProgramTacticsImpl.boxVacuousT(pos)
      Some(t)
    }

    //Returns true if this tactics is applicable to the proof node
    override def applicable(node: ProofNode): Boolean = true
  }

  val f2 = "[{t'=1,x1'=c1(x1,x2,x3,T),x2'=c2(x1,x2,x3,T),x3'=c3(x1,x2,x3,T)&H1(x1,x2,x3,T)}]A(x1,x2,x3,T)->[{t'=1,x1'=c1(x1,x2,x3,T),x2'=c2(x1,x2,x3,T),x3'=c3(x1,x2,x3,T),y1'=d1(y1,y2,y3,y4,T),y2'=d2(y1,y2,y3,y4,T),y3'=d3(y1,y2,y3,y4,T),y4'=d4(y1,y2,y3,y4,T)&H1(x1,x2,x3,T)&G1(y1,y2,y3,y4,T)}]A(x1,x2,x3,T)".asFormula
  val n2 = "Proof of Lemma2 - Drop Plant"
  val t2 = implyR(1) & lemma2(1, 3, 4, false)

  def lemma2(pos: Integer, rotate: Integer, remove: Integer, commuteEvo: Boolean): BelleExpr = "Lemma2" by ((pos:Position,sequent:Sequent)=>{
      var t = useAt("DCi inverse differential cut", PosInExpr(1 :: Nil))(pos) &
        (commaCommuteT(pos)) * (1 + rotate)
      if (commuteEvo) t = useAt(DerivedAxioms.domainCommute)(pos) & t
      t = t & (introduceForAllFromDG(pos) & useAt("DGi inverse differential ghost", PosInExpr(1 :: Nil))(pos)) * remove
      if (rotate == 0) t = t & commaCommuteT(pos)
      Some(t)
    })

    def introduceForAllFromDG(pos: Integer): BelleExpr = new ConstructionTactic("Introduce For-All from DG") {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val v = nextVariable(node.sequent.succ(pos - 1))
        Some(
          cut(Forall(Seq(v), node.sequent.succ(pos - 1))) & onBranch(
            (cutUseLbl, allL(v, v)(AntePos(node.sequent.ante.length)) & prop), (cutShowLbl, hide(pos)))
        )
      }


      private def nextVariable(f: Formula): Variable = {
        f match {
          case Box(ODESystem(ode, _), _) => ode match {
            case AtomicODE(s, _) => println("a: " + s.x); s.x
            case DifferentialProduct(a: AtomicODE, _) => println("d: " + a.xp.x); a.xp.x
          }
        }
      }

//      /** Returns true if this tactics is applicable to the proof node */
//      override def applicable(sequent: Sequent): Boolean = sequent.succ.length >= pos &&
//        (sequent.succ(pos - 1) match {
//          case Box(ODESystem(ode, _), _) => ode match {
//            case AtomicODE(s, _) => true
//            case DifferentialProduct(a: AtomicODE, _) => true
//            case _ => false
//          }
//          case _ => false
//        })
    }


  val f3 = "([x:=*;]A(x))->([x:=p;]A(x))".asFormula
  val n3 = "Proof of Lemma3 - Overapproximate Assignment"
  val t3 = ls(implyR) & ls(assignb) & la(randomb) & la(allL("x".asVariable, "x_1".asTerm)) & close(-2, 1)
  //Alternative: ls(implyR) & useAt(assignbEquationalAxiom)(1) & useAt(allSubstitute)(1) & la(randomb) & la(allL("x".asVariable, "p".asTerm)) & close(-1, 1)

  val f4 = "([x:=*;?F(x);y:=*;?G(y);]A(x,y))<->([y:=*;?G(y);x:=*;?F(x);]A(x,y))".asFormula
  val n4 = "Proof of Lemma4 - Reorder Assignment"
  val t4 = equivR(1) & onBranch(
    (equivLeftLbl, composeb(1) & composeb(1, 1 :: Nil) & composeb(1, 1 :: 1 :: Nil) & composeb(-1) & composeb(-1, 1 :: Nil) & composeb(-1, 1 :: 1 :: Nil) &
      testb(1, 1 :: Nil) & testb(1, 1 :: 1 :: 1 :: Nil) & testb(-1, 1 :: Nil) & testb(-1, 1 :: 1 :: 1 :: Nil) &
      useAt("[:*] assign nondet")(-1) & useAt("[:*] assign nondet")(1) & useAt("[:*] assign nondet")(-1, 0 :: 1 :: Nil) & useAt("[:*] assign nondet")(1, 0 :: 1 :: Nil) &
      useAt("vacuous all quantifier", PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) & useAt("all distribute", PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt("all extract", PosInExpr(1 :: Nil))(-1, 0 :: Nil) &
      useAt("commute impl", PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt("commute all", PosInExpr(1 :: Nil))(1) &
      prop
      ),
    (equivRightLbl, composeb(1) & composeb(1, 1 :: Nil) & composeb(1, 1 :: 1 :: Nil) & composeb(-1) & composeb(-1, 1 :: Nil) & composeb(-1, 1 :: 1 :: Nil) &
      testb(1, 1 :: Nil) & testb(1, 1 :: 1 :: 1 :: Nil) & testb(-1, 1 :: Nil) & testb(-1, 1 :: 1 :: 1 :: Nil) &
      useAt("[:*] assign nondet")(-1) & useAt("[:*] assign nondet")(1) & useAt("[:*] assign nondet")(-1, 0 :: 1 :: Nil) & useAt("[:*] assign nondet")(1, 0 :: 1 :: Nil)
      & useAt("all extract", PosInExpr(1 :: Nil))(1, 0 :: Nil)
      & useAt("all extract", PosInExpr(1 :: Nil))(-1, 0 :: Nil)
      & useAt("commute impl", PosInExpr(1 :: Nil))(-1, 0 :: 0 :: Nil)
      & useAt("commute all", PosInExpr(1 :: Nil))(-1)
      & prop
      )
  )

  val f5 = "[a;]F(??)->([a;?F(??);]A(??) <-> [a;]A(??))".asFormula
  val n5 = "Proof of Lemma5 - Introduce Test"
  val t5 = ls(implyR) & cut("([a;?F(??);]A(??) -> [a;]A(??)) & ([a;?F(??);]A(??) <- [a;]A(??))".asFormula) & onBranch(
    (cutUseLbl, la(andL) & ls(equivR) & onBranch(
      (equivLeftLbl, la(implyL) &&(close(-3, 2), close(-4, 1))),
      (equivRightLbl, la(implyL) &&(la(implyL) &&(close(-2, 3), close(-3, 1)), la(implyL) &&(close(-2, 2), close(-4, 1))))
    )),
    (cutShowLbl, ls(andR) &&(hideR(1) & composeb(1, List(0)) & ls(K) & Monb & ls(implyR) & la(testb) & la(implyL) &&(close(-1, 2), close(-2, 1)), hideR(1) & composeb(1, List(1)) & ls(K) & Monb & ls(implyR) & ls(testb) & ls(implyR) & close(-2, 1)))
  )

  val f6 = "(([?G(??);]A(??)) & (F(??)->G(??))) -> [?F(??);]A(??)".asFormula
  val n6 = "Proof of Lemma6 - Weaken Test"
  val t6 = ls(implyR) & la(andL) & la(testb) & ls(testb) & ls(implyR) & PropositionalTacticsImpl.modusPonensT(AntePosition(2), AntePosition(1)) & PropositionalTacticsImpl.modusPonensT(AntePosition(1), AntePosition(0)) & close

  //Corollary 1
  val f7 = "(([a;][?G(??);]A(??)) & [a;](F(??)->G(??))) ->[a;][?F(??);]A(??)".asFormula
  val n7 = "Proof of Corollary1- Weaken Test Context"
  val t7 = implyR(1) & useAt("[] split",PosInExpr(1::Nil))(-1) & Monb &  PropositionalTacticsImpl.InverseImplyRightT() & useAt(lemma("Proof of Lemma6 - Weaken Test").get,PosInExpr())(1)


  def lemma(n: String): Option[Lemma] = {
    val lemmaDB = LemmaDBFactory.lemmaDB
    lemmaDB.get(n)
  }

  def lemma(f: Formula, n: String, t: Tactic): Lemma = {
    //proved, so create lemma
    val lemmaDB = LemmaDBFactory.lemmaDB
    if (lemmaDB.contains(n)) return lemmaDB.get(n).get
    else {
      val proof = TactixLibrary.proveBy(f, t)
      if (proof.isProved) {
        val evidence = ToolEvidence(Map("input" -> proof.toString, "output" -> "true")) :: Nil
        val l = Lemma(proof, evidence, Some(n))
        lemmaDB.add(l)
        l
      }
      else
        null
    }
  }


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
      println("Verified " + n7)  }

  //  def lemma1BA(pos: Integer): Tactic = HybridProgramTacticsImpl.boxVacuousT(pos) & prop
  //  def lemma1AB(pos: Integer): Tactic = AxiomaticRuleTactics.boxMonotoneT & HybridProgramTacticsImpl.boxVacuousT(pos) & prop


  def main(args: Array[String]) {
//        proofAll


    val f=f7
    val n=n7
    val t=t7
    if (null == lemma(f, n, t))
      println(" Error proving '" + n + "'!")
    else
      println("Verified " + n)
    ProofHelper.shutdownProver
  }
}

*/