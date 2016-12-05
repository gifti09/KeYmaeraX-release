package cbcps

import java.io.{File, FileInputStream}

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentPositionTactic, Find, OnAll}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ParserFactory._

/**
  * Created by andim on 13.10.2016.
  */
class ComponentTest extends TacticTestBase {

  "ETCS" should "prove RBC component" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_rbc.kyx")))

    val invariant =
      """b>0
        | & drive=0
        | & brake=1
        |  & ep>0
        |& (
        |  state=brake
        |  & m0=m & d0=d
        |) | (
        |  state=drive
        |  & d >= 0
        |  & d0^2 - d^2 <= 2*b*(m-m0)
        |  & vdes >= 0
        |)""".stripMargin.asFormula

    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & QE & print("Base case done"),
      print("Use case") & QE & print("Use case done"),
      print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & OnAll(diffSolve(1) partial) &
        OnAll(speculativeQE) & printIndexed("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove train component" in withMathematica { implicit tool =>
    val s = parseToSequent(new FileInputStream(new File("C:\\svn-vde\\documents\\cbcps-dP-dT\\draft\\models\\examples\\components\\etcs\\multiport_train.kyx")))

    val invariant =
      """b>0
        |& drive=0
        |& brake=1
        |& ep>0
        |& v^2 - d^2 <= 2*b*(m-z)
        |& d >= 0""".stripMargin.asFormula

    //@todo proves only when notL is disabled in normalize, because diffSolve hides facts
    val tactic = implyR(1) & (andL('L) *) & loop(invariant)(1) < (
      print("Base case") & master() & print("Base case done"),
      print("Use case") & master() & print("Use case done"),
      print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & printIndexed("WTF?") & OnAll(diffSolve('R) & print("Foo") partial) &
        printIndexed("After diffSolve") & OnAll(normalize partial) & printIndexed("After normalize") & OnAll(speculativeQE) & printIndexed("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }


  ignore should "prove test" in withMathematica { implicit tool =>
    TactixLibrary.proveBy("5>2".asFormula, QE)
  }

  ignore should "prove Andreas' robot component" in withZ3 { implicit tool =>
    val model = "(t=0&v>=0&(abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B))&dx^2+dy^2=1&A>=0&B>0&V>=0&ep>0&xoIn0=xoIn&yoIn0=yoIn&t=tOld)&true->[{{{{{{xoIn0:=xoIn;yoIn0:=yoIn;}{a:=-B;++?v=0;a:=0;w:=0;++a:=*;?-B<=a&a<=A;k:=*;w:=*;?v*k=w;?abs(x-xoIn)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yoIn)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V));}}tOld:=t;}{t'=1,x'=v*dx,y'=v*dy,dx'=-w*dy,dy'=w*dx,v'=a,w'=a*k&(t<=ep&v>=0)&t-tOld<=ep}}{xoIn:=*;?-V*(t-tOld)<=xoIn-xoIn0&xoIn-xoIn0<=V*(t-tOld);}yoIn:=*;?-V*(t-tOld)<=yoIn-yoIn0&yoIn-yoIn0<=V*(t-tOld);}?true;}*]((v>0->(x-xoIn)^2+(y-yoIn)^2>0)&true)".asFormula

    def invariant(t: String) =
      s"""v >= 0
          | & dx^2+dy^2 = 1
          | & 0 <= $t & $t <= ep
          | & -V*($t) <= xoIn-xoIn0 & xoIn-xoIn0 <= V*($t) & -V*($t) <= yoIn-yoIn0 & yoIn-yoIn0 <= V*($t)
          | & (v = 0 | abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
          |          | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String, t: String): DependentPositionTactic = diffInvariant(
      s"0<=$t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*($t)".asFormula,
      s"-($t) * (v - $a/2*($t)) <= x - old(x) & x - old(x) <= ($t) * (v - $a/2*($t))".asFormula,
      s"-($t) * (v - $a/2*($t)) <= y - old(y) & y - old(y) <= ($t) * (v - $a/2*($t))".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide = true)('Llast) * 3 /* 3 old(...) in DI */ & (andL('_) *) &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule *) & printIndexed("Before replaceTransform") &
      replaceTransform("ep".asTerm, "(t-tOld)".asTerm)(-10) & print("After replaceTransform") &
      speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('R) & (andL('L) *) & loop(invariant("t-tOld"))('R) < (
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & print("After chase") & normalize(andR('R), skip, skip) & printIndexed("After normalize") < (
      print("Braking branch") & di("-B", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(andR('R), skip, skip) & print("After braking normalize") & OnAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di("0", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(andR('R), skip, skip) & OnAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(betaRule, skip, skip) & print("After acc normalize") & OnAll(hideFactsAbout("dx", "dy", "k", "k_0") partial) < (
        hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic,
        hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(model, tactic) shouldBe 'proved
  }


}
