package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics._
import edu.cmu.cs.ls.keymaerax.core.{Variable, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics]]
 */
class EqualityTests extends TacticTestBase {

  "eqL2R" should "rewrite x*y=0 to 0*y=0 using x=0" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "0*y=0".asFormula
  }

  it should "rewrite entire formula" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=x&x+1=1".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0&0+1=1".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite entire formula at specified position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=x&x+1=1".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0&x+1=1".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite entire term at specified position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*x*y=x".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*0*y=x".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite only at very specified position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=x".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1, 0::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=x".asFormula, "x+1>0".asFormula)
  }

  it should "keep positions stable" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula, "x+1>0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ shouldBe IndexedSeq("0*y=0".asFormula, "x+1>0".asFormula)
  }

  it should "rewrite complicated" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0 & x+3>2 | \\forall y y+x>=0".asFormula)), eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0".asFormula
  }

  it should "rewrite complicated exhaustively" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0 & x+3>2 | \\forall y y+x>=0 & \\exists x x>0".asFormula)),
      eqL2R(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0 & \\exists x x>0".asFormula
  }

  it should "rewrite x*y=0 to 0*y=0 using 0=x" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("0=x".asFormula), IndexedSeq("x*y=0".asFormula)),
      TactixLibrary.useAt("= commute")(-1) & eqL2R(-1)(1) & TactixLibrary.useAt("= commute")(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "0=x".asFormula
    result.subgoals.head.succ should contain only "0*y=0".asFormula
  }

  it should "rewrite only some of the symbols when asked to" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("y=x".asFormula), IndexedSeq("y=2&y+y+2>y+1".asFormula)),
      eqL2R(-1)(1, 0::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "y=x".asFormula
    result.subgoals.head.succ should contain only "x=2&y+y+2>y+1".asFormula
  }

  "eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("0=x".asFormula), IndexedSeq("x*y=0".asFormula)), eqR2L(-1)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "0=x".asFormula
    result.subgoals.head.succ should contain only "0*y=0".asFormula
  }

  "Exhaustive eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in {
    val result = proveBy(Sequent(IndexedSeq("0=x".asFormula), IndexedSeq("x*y=0".asFormula)), exhaustiveEqR2L(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "0=x".asFormula
    result.subgoals.head.succ should contain only "0*y=0".asFormula
  }

  "Exhaustive eqL2R" should "rewrite a single formula exhaustively" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula, "z<x+1".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "not fail when there are no applicable positions" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("z>2".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "z>2".asFormula
  }

  it should "rewrite a single formula exhaustively for a single applicable position" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula)
  }

  it should "rewrite formulas exhaustively" in {
    val result = proveBy(Sequent(IndexedSeq("x=0".asFormula, "z=x".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula, "z<x+1".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=0".asFormula, "z=0".asFormula)
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively everywhere" in {
    val result = proveBy(Sequent(IndexedSeq("z=x".asFormula, "x=0".asFormula), IndexedSeq("x*y=0".asFormula, "z>2".asFormula, "z<x+1".asFormula)), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=0".asFormula, "z=0".asFormula)
    result.subgoals.head.succ should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "work even if there is only one other formula" in {
    val result = proveBy(Sequent(IndexedSeq("x<5".asFormula, "x=0".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("0<5".asFormula, "x=0".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  it should "replace arbitary terms" in {
    val result = proveBy(Sequent(IndexedSeq("a+b<5".asFormula, "a+b=c".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("c<5".asFormula, "a+b=c".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in {
    a [BelleThrowable] should be thrownBy proveBy(Sequent(IndexedSeq("0<5".asFormula, "0=0".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
  }

  it should "not try to rewrite bound occurrences" in {
    val result = proveBy(Sequent(IndexedSeq("a=1".asFormula), IndexedSeq("[a:=2;]a=1".asFormula)), exhaustiveEqL2R(-1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a=1".asFormula
    result.subgoals.head.succ should contain only "[a:=2;]a=1".asFormula
  }

  it should "rewrite multiple occurrences of a term in one shot" in {
    val result = proveBy(Sequent(IndexedSeq("x+2<=x+3".asFormula, "x=y".asFormula), IndexedSeq()), exhaustiveEqL2R(-2))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe IndexedSeq("y+2<=y+3".asFormula, "x=y".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "Abbrv tactic" should "abbreviate a+b to z" in withMathematica { qeTool =>
    val result = proveBy("a+b < c".asFormula, abbrv(Variable("z"))(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z = a+b".asFormula
    result.subgoals.head.succ should contain only "z < c".asFormula
  }

  it should "abbreviate min(a,b) to z" in withMathematica { qeTool =>
    val result = proveBy("min(a,b) < c".asFormula, abbrv(Variable("z"))(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "z = min(a,b)".asFormula
    result.subgoals.head.succ should contain only "z < c".asFormula
  }

  it should "not abbreviate in places where at least one of the arguments is bound" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("min(a,b) < c".asFormula), IndexedSeq("[a:=0;]min(a,b) < c".asFormula)),
      abbrv(Variable("z"))(-1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("z = min(a,b)".asFormula, "z < c".asFormula)
    result.subgoals.head.succ should contain only "[a:=0;]min(a,b) < c".asFormula
  }

  it should "abbreviate min(a,b) to z everywhere (except at bound occurrences)" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("min(a,b) < c".asFormula, "x>y".asFormula, "5 < min(a,b)".asFormula), IndexedSeq("min(a,b) + 2 = 7".asFormula, "a<b".asFormula, "[b:=2;]min(a,b) < 9".asFormula)), abbrv(Variable("z"))(-1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("z = min(a,b)".asFormula, "z<c".asFormula, "x>y".asFormula, "5<z".asFormula)
    result.subgoals.head.succ should contain only ("z+2=7".asFormula, "a<b".asFormula, "[b:=2;]min(a,b)<9".asFormula)
  }

  //@todo input tactic with optional arguments
  it should "abbreviate min(a,b) to z everywhere (except at bound occurrences) and pick a name automatically" ignore withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("min(a,b) < c".asFormula, "x>y".asFormula, "5 < min(a,b)".asFormula), IndexedSeq("min(a,b) + 2 = 7".asFormula, "a<b".asFormula, "[b:=2;]min(a,b) < 9".asFormula)), abbrv("min(a,b)".asTerm))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("min_0 = min(a,b)".asFormula, "min_0<c".asFormula, "x>y".asFormula, "5<min_0".asFormula)
    result.subgoals.head.succ should contain only ("min_0+2=7".asFormula, "a<b".asFormula, "[b:=2;]min(a,b)<9".asFormula)
  }

  //@todo input tactic with optional arguments
  it should "abbreviate any argument even if not contained in the sequent and pick a name automatically" ignore withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>y".asFormula), IndexedSeq("a<b".asFormula)), abbrv("c+d".asTerm))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0 = c+d".asFormula, "x>y".asFormula)
    result.subgoals.head.succ should contain only "a<b".asFormula
  }

  "abs" should "expand abs(x) in succedent" in withMathematica { qeTool =>
    val result = proveBy("abs(x) >= 5".asFormula, abs(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=0&abs_0=x | x<0&abs_0=-x".asFormula
    result.subgoals.head.succ should contain only "abs_0>=5".asFormula
  }

  it should "expand abs(x) in non-top-level succedent" in withMathematica { qeTool =>
    val result = proveBy("y=2 | abs(x) >= 5".asFormula, abs(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=0&abs_0=x | x<0&abs_0=-x".asFormula
    result.subgoals.head.succ should contain only "y=2 | abs_0>=5".asFormula
  }

  it should "expand abs(x) in antecedent" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("abs(x) >= 5".asFormula), IndexedSeq()), abs(-1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>=0&abs_0=x | x<0&abs_0=-x".asFormula, "abs_0>=5".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "min" should "expand min(x,y) in succedent" in withMathematica { qeTool =>
    val result = proveBy("min(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x<=y&min_0=x | x>y&min_0=y".asFormula
    result.subgoals.head.succ should contain only "min_0>=5".asFormula
  }

  it should "expand min(x,y) in antecedent" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("min(x,y) >= 5".asFormula), IndexedSeq()), minmax(-1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x<=y&min_0=x | x>y&min_0=y".asFormula, "min_0>=5".asFormula)
    result.subgoals.head.succ shouldBe empty
  }

  "max" should "expand max(x,y) in succedent" in withMathematica { qeTool =>
    val result = proveBy("max(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=y&max_0=x | x<y&max_0=y".asFormula
    result.subgoals.head.succ should contain only "max_0>=5".asFormula
  }

  it should "expand max(x,y) in antecedent" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("max(x,y) >= 5".asFormula), IndexedSeq()), minmax(-1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x>=y&max_0=x | x<y&max_0=y".asFormula, "max_0>=5".asFormula)
    result.subgoals.head.succ shouldBe empty
  }
}
