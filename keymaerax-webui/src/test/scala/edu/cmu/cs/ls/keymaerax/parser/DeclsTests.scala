package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}
import org.scalatest.LoneElement._

/**
  * Tests the declarations parser.
  * Created by nfulton on 9/1/15.
  */
class DeclsTests extends FlatSpec with Matchers {
  "Declarations parser" should "parse declarations block correctly." in {
    val input =
      """ProgramVariables.
        |R x.
        |R z.
        |R z_0.
        |End.
      """.stripMargin
    val d = KeYmaeraXDeclarationsParser(KeYmaeraXLexer.inMode(input, ProblemFileMode))._1
    d.decls.keySet.contains("x", None) shouldBe true
    d.decls.keySet.contains("z", None) shouldBe true
    d.decls.keySet.contains("z", Some(0)) shouldBe true
    d.decls.keys.toList.length shouldBe 3
  }

  it should "parse declarations of z, z_0 as two separate declarations" in {
    val input =
      """ProgramVariables.
        |R x.
        |R z.
        |R z_0.
        |R a.
        |End.
        |Problem.
        |x + z + z_0 = z_0 + z + x
        |End.
      """.stripMargin
    KeYmaeraXProblemParser(input)
  }

  "Problem/Solution Block" should "parse correctly" in {
    val input =
      """
        |Functions.
        |  B A().
        |End.
        |Problem.
        |  !(A() | !A()) -> !!(A() | !A())
        |End.
        |Solution.
        |  implyR(1)
        |End.
      """.stripMargin

    val (problem, solution) = KeYmaeraXProblemParser.parseProblemAndTactic(input)

    problem shouldBe "!(A() | !A()) -> !!(A() | !A())".asFormula
    solution shouldBe TactixLibrary.implyR(1)
  }

  "function domain" should "parse correctly" in {
    val input =
      """
        |Functions.
        |  B Cimpl(R, R, R).
        |End.
        |Problem.
        |  Cimpl(0,1,2) <-> true
        |End.
      """.stripMargin

    KeYmaeraXProblemParser(input) shouldBe Equiv(
      PredOf(Function("Cimpl", None, Tuple(Real, Tuple(Real, Real)), Bool), Pair(Number(0), Pair(Number(1), Number(2)))),
      True)
  }

  it should "fail to parse when the function application has the wrong assoc" in {
    val input =
      """
        |Functions.
        |  B Cimpl(R, R, R).
        |End.
        |Problem.
        |  Cimpl((0,1),2) <-> true
        |End.
      """.stripMargin

    a [ParseException] shouldBe thrownBy(KeYmaeraXProblemParser(input))
  }

  it should "fail to parse when the function def'n has the wrong assoc" in {
    val input =
      """
        |Functions.
        |  B Cimpl((R, R), R).
        |End.
        |Problem.
        |  Cimpl(0,1,2) <-> true
        |End.
      """.stripMargin

    a [ParseException] shouldBe thrownBy(KeYmaeraXProblemParser(input))
  }

  it should "parse correctly when fully explicit" in {
    val input =
      """
        |Functions.
        |  B Cimpl((R, R), R).
        |End.
        |Problem.
        |  Cimpl((0,1),2) <-> true
        |End.
      """.stripMargin

    val input2 =
      """
        |Functions.
        |  B Cimpl(R, (R, R)).
        |End.
        |Problem.
        |  Cimpl(0,(1,2)) <-> true
        |End.
      """.stripMargin

    KeYmaeraXProblemParser(input) shouldBe "Cimpl((0,1),2) <-> true".asFormula
    KeYmaeraXProblemParser(input2) shouldBe "Cimpl(0,(1,2)) <-> true".asFormula
  }

  it should "substitute in definitions" in {
    val input =
      """
        |Functions.
        |  B Pred(R, R, R) <-> ( (._0) + (._1) <= (._2) ).
        |End.
        |Problem.
        |  Pred(0,1,2) <-> true
        |End.
      """.stripMargin

    val (decls, formula) = KeYmaeraXProblemParser.parseProblem(input)
    decls.decls.loneElement._2 match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Tuple(Real, Tuple(Real, Real))
      codomain shouldBe Bool
      interpretation shouldBe "(._0) + (._1) <= (._2)".asFormula
    }
    formula shouldBe "0+1 <= 2 <-> true".asFormula
  }

  "Declarations type analysis" should "elaborate variables to no-arg functions per declaration" in {
    val model = """Functions.
                  |  R b().
                  |  R m().
                  |End.
                  |
                  |ProgramVariables.
                  |  R x.
                  |  R v.
                  |  R a.
                  |End.
                  |
                  |Problem.
                  |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
                  |End.
                  |""".stripMargin
    val m = FuncOf(Function("m", None, Unit, Real), Nothing)
    val b = FuncOf(Function("b", None, Unit, Real), Nothing)
    val x = Variable("x")
    val a = Variable("a")
    val v = Variable("v")
    KeYmaeraXProblemParser(model) shouldBe Imply(
      And(LessEqual(x, m), Greater(b, Number(0))),
      Box(Compose(Assign(a, Neg(b)), ODESystem("{x'=v,v'=a}".asDifferentialProgram, GreaterEqual(v, Number(0)))), LessEqual(x, m)))
  }

  it should "not allow variables refer to functions with parameters" in {
    val model = """Functions.
                  |  R b(R).
                  |  R m(R,R).
                  |End.
                  |
                  |ProgramVariables.
                  |  R x.
                  |  R v.
                  |  R a.
                  |End.
                  |
                  |Problem.
                  |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
                  |End.
                  |""".stripMargin
    a[ParseException] should be thrownBy KeYmaeraXProblemParser(model)
  }

  it should "succeed when ()'s are used." in {
    val model = """Functions.
                  |  R b().
                  |  R m().
                  |End.
                  |
                  |ProgramVariables.
                  |  R x.
                  |  R v.
                  |  R a.
                  |End.
                  |
                  |Problem.
                  |  x<=m() & b()>0 -> [a:=-b(); {x'=v,v'=a & v>=0}]x<=m()
                  |End.
                  |""".stripMargin
    KeYmaeraXProblemParser(model) shouldBe "x<=m() & b()>0 -> [a:=-b(); {x'=v,v'=a & v>=0}]x<=m()".asFormula
  }

  it should "detect and print undeclared symbols" in {
    val model = """Problem. x>0 End."""
    //@todo better location information
    the [ParseException] thrownBy  KeYmaeraXProblemParser(model) should have message
      """<somewhere> type analysis: undefined symbol x with index None
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
  }
}
