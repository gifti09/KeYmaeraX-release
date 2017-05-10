package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, SummaryTest, TodoTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import edu.cmu.cs.ls.keymaerax.tools.ToolException
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.IndexedSeq

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.ODE]] differential equations proving.
 */
@UsualTest
class ODETests extends TacticTestBase {
  "ODE" should "prove x=0 -> [{x'=-x}]x=0" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x=0 -> [{x'=-x}]x=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  "Pretest" should "PDEify x^2+y^2=1&e=x -> [{x'=-y,y'=e,e'=-y}](x^2+y^2=1&e=x)" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x^2+y^2=1&e=x -> [{x'=-y,y'=e,e'=-y}](x^2+y^2=1&e=x)".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "autocut x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "solve to prove x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0" in withMathematica {qeTool =>
    TactixLibrary.proveBy("x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0".asFormula, implyR(1) & ODE(1) & onAll(QE)) shouldBe 'proved
  }

  it should "DI to prove w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9" in withMathematica {qeTool =>
    TactixLibrary.proveBy("w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  "openDiffInd" should "directly prove x>0 -> [{x'=x}]x>0" in withMathematica { qeTool =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  "DGauto" should "DGauto x>0 -> [{x'=-x}]x>0 by DA" in withMathematica { qeTool =>
    proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  //  ignore should "DGauto x_>0 -> [{x_'=-x_}]x_>0 by DA" in withMathematica { qeTool =>
  //    proveBy("x_>0 -> [{x_'=-x_}]x_>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  //  }

  it should "DGauto x>0->[{x'=-x+1}]x>0" in withMathematica { qeTool =>
    //@note: ghost is y'=1/2*y for x*y^2>0
    proveBy("x>0->[{x'=-x+1}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0&a()>0->[{x'=-a()*x}]x>0" in withMathematica { qeTool =>
    proveBy("x>0&a()>0->[{x'=-a()*x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0&a>0->[{x'=-a*x}]x>0" in withMathematica { qeTool =>
    proveBy("x>0&a>0->[{x'=-a*x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0" in withMathematica { qeTool =>
    proveBy("x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0->[{x'=-a*x,a'=4&a>0}]x>0" in withMathematica { qeTool =>
    proveBy("x>0->[{x'=-a*x,a'=4&a>0}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0 |- [{x'=2}]x>0" in withMathematica { tool =>
    //@note: ghost is y'=x*y for x*y^2>0
    proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>0".asFormula)), DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>b() |- [{x'=2}]x>b()" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x>b()".asFormula), IndexedSeq("[{x'=2}]x>b()".asFormula)), DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>b |- [{x'=2}]x>b" taggedAs (TodoTest) in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), DGauto(1)) shouldBe 'proved
  }


  "Auto ODE" should "prove x>0 -> [{x'=x}]x>0" taggedAs(SummaryTest) in withMathematica { qeTool =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }
  it should "prove x>0 -> [{x'=x}]x>0 with lengthy tactic" in withMathematica { qeTool =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, (implyR(1) & ODE(1) & (onAll(QE) | done)) | skip) shouldBe 'proved
  }
  it should "prove x>0 -> [{x'=x}]x>0 with lengthy tactic 2" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x>0 -> [{x'=x}]x>0".asFormula, (implyR(1) & ODE(1) & (onAll(QE) | done)) | skip) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5" in withMathematica { qeTool =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "split and prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withMathematica { qeTool =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & boxAnd(1) & andR(1) <(
      ODE(1),
      ODE(1)
      )) shouldBe 'proved
  }

  it should "split and on all prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withMathematica { qeTool =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & boxAnd(1) & andR(1) & onAll(
      ODE(1)
      )) shouldBe 'proved
  }

  it should "split* and on all prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withMathematica { qeTool =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & ((boxAnd(1) & andR(1))*) & onAll(
      ODE(1)
    )) shouldBe 'proved
  }

  it should "prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withMathematica { qeTool =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "prove x>0 -> [{x'=-x}]x>0 by DA" taggedAs(SummaryTest) in withMathematica { qeTool =>
    proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "prove x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0" in withMathematica { qeTool =>
    proveBy("x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "PDEify to prove x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" in withMathematica { qeTool =>
    TactixLibrary.proveBy("x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "work with nested ODEs" in withMathematica { _ =>
    proveBy("x>0 -> [{x'=5};{x'=2};{x'=x}]x>0".asFormula, (unfoldProgramNormalize & ODE(1))*3) shouldBe 'proved
  }

  it should "work with solvable maybe bound" in withMathematica { _ =>
    val result = proveBy("[{x'=5}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula, ODE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain theSameElementsAs List("\\forall t_ (t_>=0 -> \\forall x (x=5*t_+x_1 -> [{x:=x+3;}* ++ y:=x;](x>0&y>0)))".asFormula)
  }

  it should "work with maybe bound" in withMathematica { _ =>
    val result = proveBy("x>0 -> [{x'=-x}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula,
      implyR(1) & DifferentialTactics.ODE(introduceStuttering=true, dW(1) & assignb(1, 1::Nil))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain theSameElementsAs List("true&x>0 -> [{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula)
  }

  it should "not stutter repeatedly" in withMathematica { _ =>
    val result = proveBy("[{x'=x^x}]x>0".asFormula, ODE(1) | skip)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain theSameElementsAs "[{x'=x^x}]x>0".asFormula::Nil
  }

  it should "prove cheat sheet example" in withMathematica { qeTool => {
    val f = KeYmaeraXProblemParser(
      """
        |/* Example from KeYmaera X Cheat Sheet */
        |Functions.        /* function symbols cannot change their value */
        |    R A.          /* real-valued maximum acceleration constant */
        |    R B.          /* real-valued maximum braking constant */
        |End.
        |
        |ProgramVariables. /* program variables may change their value over time */
        |    R x.          /* real-valued position */
        |    R v.          /* real-valued velocity */
        |    R a.          /* current acceleration chosen by controller */
        |End.
        |
        |Problem.                               /* conjecture in differential dynamic logic */
        |    v>=0 & A>0 & B>0                   /* initial condition */
        |  ->                                   /* implies */
        |  [                                    /* all runs of hybrid system dynamics */
        |    {                                  /* braces {} for grouping of programs */
        |      {?v<=5;a:=A; ++ a:=0; ++ a:=-B;} /* nondeterministic choice of acceleration a */
        |      {x'=v, v'=a & v>=0}              /* differential equation system with domain */
        |    }* @invariant(v>=0)                /* loop repeats, with invariant contract */
        |  ] v>=0                               /* safety/postcondition */
        |End.
      """.stripMargin
    )

    val t =
      """
        |implyR(1) ; andL(-1) ; andL(-2) ; loop({`v>=0`}, 1) ; <(
        |  master,
        |  master,
        |  composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; ODE(1),
        |    choiceb(1) ; assignb(1.0) ; assignb(1.1) ; andR(1) ; <(
        |      solve(1) ; master,
        |      solve(1) ; master
        |      )
        |    )
        |  )
      """.stripMargin.asTactic

    TactixLibrary.proveBy(f, t) shouldBe 'proved


  }}

  //@note: there's overlap as multiple methods are able to prove some of the following examples
  val list =
  // solvable cases
    "x>=0&v=1 -> [{x'=v}]x>=0" ::
      "x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0" ::
      "x>0&v=1 -> [{x'=v}]x>0" ::
      "x>0&v=1&a=2 -> [{x'=v,v'=a}]x>0" ::
      "x>0&v=1&a=2 -> [{x'=v,v'=a&v>=0}](x>0&v>=0)" ::
      "x>1&v=10&a=-2 -> [{x'=v,v'=a&v>=0}](x>1&v>=0)" ::
      "x>=1&v=10&a=-2 -> [{x'=v,v'=a&v>=0}](x>=1&v>=0)" ::
      "x>b -> [{x'=2}]x>b" ::
      // open cases
      "x^2>5 -> [{x'=x^3}]x^2>5" ::
      "5<x^2 -> [{x'=x^3}]5<x^2" ::
      "x^3>5 -> [{x'=x^4}]x^3>5" ::
      "5<x^3 -> [{x'=x^4}]5<x^3" ::
      "x^3>5 -> [{x'=x^3+x^4}]x^3>5" ::
      "5<x^3 -> [{x'=x^3+x^4}]5<x^3" ::
      "x>0->[{x'=x+5}]x>0" ::
      "x>0->[{x'=x^2+5}]x>0" ::
      "x^3>0->[{x'=x+5}]x^3>0" ::
      "x^3>0->[{x'=x^2+5}]x^3>0" ::
      "y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}]y>2" ::
      "y^3>2 -> [{x'=x^3+x^4,y'=5*y+y^2}]y^3>2" ::
      "y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}]y^3>2" ::
      // split open cases
      "x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" ::
      // split cases
      "x>=1&y=10&a=-2 -> [{x'=y,y'=a+y^2-y&y>=0}](x>=1&y>=0)" ::
      // auto-ghost
      "x>0->[{x'=-x}]x>0" ::
      "x>0->[{x'=x}]x>0" ::
      "x>0->[{x'=-5*x}]x>0" ::
      "x>0->[{x'=5*x}]x>0" ::
      "x>0->[{x'=x+1}]x>0" ::
      "z>0->[{z'=-z}]z>0" ::
      "z>0->[{z'=z}]z>0" ::
      "z>0->[{z'=z+1}]z>0" ::
      //"x>0->[{x'=-x+1}]x>0" ::
      "x>0&a()>0->[{x'=-a()*x}]x>0" ::
      "x>0&a>0->[{x'=-a*x}]x>0" ::
      "x>0->[{x'=-a*x,a'=4&a>0}]x>0" ::
      "x>0->[{x'=-a*x,a'=-4&a>0}]x>0" ::
      "x>0&a()<0->[{x'=a()*x}]x>0" ::
      "x>0&a<0->[{x'=a*x}]x>0" ::
      "x>0&a()>0&c()<0->[{x'=a()*c()*x}]x>0" ::
      "x>0&a>0&c<0->[{x'=a*c*x}]x>0" ::
      "x>0&a>0&b>=0->[{x'=a*x+b}]x>0" ::
      //"x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0" ::
      //"x>0&a<0&b>=0->[{x'=a*x+b}]x>0" ::
  // conserved quantity
      "x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c -> [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c" ::
  // diffcut
      //"x>=0&y>0&a>0->[{x'=y,y'=y*a}]x>=0" ::
      // misc
      "x>0->[{x'=-x+1}]x>0" ::
      "x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0" ::
      "x>0&a<0&b>=0->[{x'=a*x+b}]x>0" ::
      "x^3>0&a<0&b>0->[{x'=a*x+b}]x^3>0" ::
      "x>0->[{x'=x^3+x}]x>0" ::
      "x>0->[{x'=-x^3-x}]x>0" ::
      "x^3>0->[{x'=x^3+x^4}]x^3>0" ::
      "x^3>0->[{x'=-x^3-x^4}]x^3>0" ::
      // exams
      "x>=1|x^3>=8->[{x'=x^4+x^2}](x>=1|x^3>=8)" ::
      "x^3-4*x*y>=99->[{x'=4*x,y'=3*x^2-4*y}]x^3-4*x*y>=99" ::
      "x^3-4*x*y=100->[{x'=4*x,y'=3*x^2-4*y}]x^3-4*x*y=100" ::
      //"x>=2&y>=22->[{x'=4*x^2,y'=x+y^4}]y>=22" ::
      "w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9" ::
      //"x>=2&y=1->[{x'=x^2+y+x^4,y'=y^2+1}]x^3>=1" ::
      //"x=-1&y=1->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0" ::
      //"x>=2&y=1->[{x'=x^2*y^3+x^4*y,y'=y^2+2*y+1}]x^3>=8" ::
      //"x-x^2*y>=2&y!=5->[{x'=-x^3,y'=-1+2*x*y}]x-x^2*y>=2" ::
      //"x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" ::
      "x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0" ::
      "x>=0&y>0&a>0->[{x'=y,y'=y*a}]x>=0" ::
      "x>=2&y>=22->[{x'=4*x^2,y'=x+y^4}]y>=22" ::
      "x>=2&y>=0->[{x'=x^2+y+x^4,y'=y^2+1}]x^3>=1" ::
      "x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" ::
      "x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0" ::
      "x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0" ::
      // ITP'12
      "x^2+y^2=1&e=x -> [{x'=-y,y'=e,e'=-y}](x^2+y^2=1&e=x)" ::
      "d1^2+d2^2=w()^2*p^2&d1=-w()*x2&d2=w()*x1 -> [{x1'=d1,x2'=d2,d1'=-w()*d2,d2'=w()*d1}](d1^2+d2^2=w()^2*p^2&d1=-w()*x2&d2=w()*x1)" ::
      "d1^2+d2^2=w^2*p^2&d1=-w*x2&d2=w*x1 -> [{x1'=d1,x2'=d2,d1'=-w*d2,d2'=w*d1}](d1^2+d2^2=w^2*p^2&d1=-w*x2&d2=w*x1)" ::
      Nil

  val nops: List[String] =
      "x=-1&y>=0->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0" ::
      "x=-1&y=1->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0" ::
      "x-x^2*y>=2&y!=5->[{x'=-x^3,y'=-1+2*x*y}]x-x^2*y>=2" ::
      "x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" ::
        "x>=1->[{x'=x^2+2*x^4}]x^3>=x^2" :: // @generalize(x>=1)&dI
        Nil


  it should "prove a list of ODEs" in withMathematica { qeTool =>
    proveAll(list)
  }

  it should "prove a list of ODEs with cuts after improving tactics" taggedAs(TodoTest) in withMathematica { qeTool =>
    proveAll(nops)
  }

  private def proveAll(list: List[String]) = {
    var fail: List[String] = Nil
    for (ex <- list) {
      val fml = ex.asFormula
      println("\nProving\n" + fml)
      val proof = TactixLibrary.proveBy(fml, (implyR(1) & ODE(1) & onAll(QE)) | skip)
      if (proof.isProved)
        println("\nProved: " + fml)
      else {
        println(proof)
        println("\nFailed: " + fml)
        fail = fail :+ ex
      }
    }
    if (fail.isEmpty)
      println("All examples proved successfully")
    else {
      println("\n\nSuccesses:\n" + list.filter(x => !fail.contains(x)).mkString("\n"))
      println("\n\nFailures:\n" + fail.mkString("\n"))
      fail shouldBe 'empty
    }
  }

  "splitWeakInequality" should "split x>=0->[{x'=x}]x>=0" in withMathematica(_ => {
    val f = "x>=0->[{x'=x}]x>=0".asFormula
    val result = proveBy(f, implyR(1) & DifferentialTactics.splitWeakInequality(1))
    result.subgoals.length shouldBe 2
    result.subgoals(0).succ.last shouldBe "[{x'=x&true}]x>0".asFormula
    result.subgoals(1).succ.last shouldBe "[{x'=x&true}]x=0".asFormula
  })

  it should "prove x>=0->[{x'=x}]x>=0 via ODE" in withMathematica(_ => {
    val f = "x>=0->[{x'=x}]x>=0".asFormula
    proveBy(f, implyR(1) & ODE(1) & onAll(QE)) shouldBe 'proved
  })
}
