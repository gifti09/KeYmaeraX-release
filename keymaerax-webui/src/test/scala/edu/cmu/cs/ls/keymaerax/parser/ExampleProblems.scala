/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Formula, FuncOf, Function, Number, Pair, Plus, PrettyPrinter, Program,
Real, Times, Trafo, Tuple, Unit}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
 * @author Nathan Fulton
 */
class ExampleProblems extends FlatSpec with Matchers {
  "parser line messages" should "be properly offset" in {
    val f =
      """|   ProgramVariables.
        |   R x. R y. R z.
        |   End.
        |   Problem.
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |   ->
        |   [
        |   {x := 2x; y := 2y;}
        |  ]
        | (x*y >= 0)
        |End.""".stripMargin

    val ex = the [ParseException] thrownBy KeYmaeraXProblemParser(f)
    ex.found shouldBe """x (ID("x"))"""
    ex.expect shouldBe "Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term"
    ex.loc.begin.line shouldBe 8
    ex.loc.begin.column shouldBe 11
  }

  it should "be properly offset in another example" in {
    val f =
      """ ProgramVariables.
        |
        |   R x. R y. R z.
        |
        |   End.
        |
        |   Problem.
        |
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |
        |   ->
        |
        |   [
        |
        |   {x := 2x; y := 2y;}
        |
        |  ]
        |
        | (x*y >= 0)
        |
        |End.""".stripMargin

    val ex = the [ParseException] thrownBy KeYmaeraXProblemParser.parseAsProblemOrFormula(f)
    ex.found shouldBe """x (ID("x"))"""
    ex.expect shouldBe "Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term"
    ex.loc.begin.line shouldBe 15
    ex.loc.begin.column shouldBe 11
  }

  it should "work from file input" in {
    val f = " ProgramVariables.\n\n   R x. R y. R z. \n\n   End.  \n\n   Problem.\n\n   (x*x*y >= 0 & x >= 0 & z >= x) \n\n   -> \n\n   [\n\n   {x := 2x; y := 2y;}\n\n  ]\n\n (x*y >= 0)\n\nEnd."

    val ex = the [ParseException] thrownBy KeYmaeraXProblemParser.parseAsProblemOrFormula(f)
    ex.found shouldBe """x (ID("x"))"""
    ex.expect shouldBe "Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term"
    ex.loc.begin.line shouldBe 15
    ex.loc.begin.column shouldBe 11
  }

  "The Parser" should "parse a simple file" in {
    val theProblem =
      """
        |ProgramVariables.
        |  R x.
        |  R y.
        |End.
        |Functions.
        |  R f(R, B).
        |  R g(B).
        |End.
        |Problem.
        |  x > 0 ->
        |  [
        |   x := x + 1;
        |  ] x > 0
        |End.
      """.stripMargin

    val result = KeYmaeraXProblemParser(theProblem)
    result shouldBe KeYmaeraXParser("""  x > 0 ->
                                      |  [
                                      |   x := x + 1;
                                      |  ] x > 0""".stripMargin)
  }

  it should "parse x>0 -> \\exists d [{x'=d}]x>0" in {
    val problem = "x>0 -> \\exists d [{x'=d}]x>0"
    val declProblem =
      s"""
        |ProgramVariables.
        |  R x.
        |End.
        |
        |Problem.
        |  $problem
        |End.
      """.stripMargin

    KeYmaeraXProblemParser(declProblem) shouldBe KeYmaeraXParser(problem)
  }

  "Interpretation parser" should "parse simple function declarations" in {
    val problem =
      """
        |Functions.
        |  R f() = (5).
        |End.
        |
        |Problem.
        |  f()>3
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Real
      interpretation shouldBe Number(5)
    }
    formula shouldBe KeYmaeraXParser("5>3")
  }

  it should "parse function declarations with one parameter" in {
    val problem =
      """
        |Functions.
        |  R f(R) = (5 + .*.).
        |End.
        |
        |Problem.
        |  f(4)>3
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Real
      codomain shouldBe Real
      interpretation shouldBe Plus(Number(5), Times(DotTerm(Real), DotTerm(Real)))
    }
    formula shouldBe KeYmaeraXParser("5+4*4>3")
  }

  it should "parse n-ary function declarations" in {
    val problem =
      """
        |Functions.
        |  R f(R,R,R) = (._0 + ._1*._2).
        |End.
        |
        |Problem.
        |  f(2,3,4)>3
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Tuple(Real, Tuple(Real, Real))
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real, Some(0)), Times(DotTerm(Real, Some(1)), DotTerm(Real, Some(2))))
    }
    formula shouldBe KeYmaeraXParser("2+3*4>3")
  }

  it should "detect undeclared dots" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """
        |Functions.
        |  R f(R,R,R) = (._1 + ._2*._3).
        |End.
        |
        |Problem.
        |  f(2,3,4)>3
        |End.
      """.stripMargin

    val thrown = the [ParseException] thrownBy KeYmaeraXProblemParser.parseProblem(problem)
    thrown.getMessage should include ("Function/predicate f((•_0,(•_1,•_2))) defined using undeclared •_3")
  }

  it should "replace names with the appropriate dots" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """Functions.
        |  R f(R x, R y, R z) = (x + y*z).
        |End.
        |
        |Problem.
        |  f(2,3,4)>3
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Tuple(Real, Tuple(Real, Real))
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real, Some(0)), Times(DotTerm(Real, Some(1)), DotTerm(Real, Some(2))))
    }
    formula shouldBe KeYmaeraXParser("2+3*4>3")
  }

  it should "not confuse arguments of same name across definitions" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """Definitions.
        |  R f(R x, R y, R z) = (x+y*z).
        |  R g(R a, R x, R y) = (f(x,y,a)).
        |End.
        |
        |Problem.
        |  f(1,2,3)>0 -> g(3,1,2)>0
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 2
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Tuple(Real, Tuple(Real, Real))
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real, Some(0)), Times(DotTerm(Real, Some(1)), DotTerm(Real, Some(2))))
    }
    d.decls should contain key ("g", None)
    d.decls(("g", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Tuple(Real, Tuple(Real,Real))
      codomain shouldBe Real
      interpretation shouldBe FuncOf(Function("f", None, Tuple(Real, Tuple(Real, Real)), Real),
        Pair(DotTerm(Real, Some(1)), Pair(DotTerm(Real, Some(2)), DotTerm(Real, Some(0)))))
    }
    formula shouldBe KeYmaeraXParser("1+2*3>0 -> 1+2*3>0")
  }

  it should "correctly dottify in the presence of unused arguments" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """Definitions.
        |  R f(R x, R y) = (y+3).
        |End.
        |
        |Problem.
        |  f(1,2)>0
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Tuple(Real, Real)
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real, Some(1)), Number(3))
    }
    formula shouldBe KeYmaeraXParser("2+3>0")
  }

  it should "replace argument name of unary function with non-indexed dot (for backwards compatibility)" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """Functions.
        |  R f(R x) = (x + 2).
        |End.
        |
        |Problem.
        |  f(2)>3
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Real
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real), Number(2))
    }
    formula shouldBe KeYmaeraXParser("2+2>3")
  }

  it should "allow both . and explicit ._0 in unary function definition" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    def problem(dot: String): String =
      s"""Functions.
        |  R f(R) = ($dot + 2).
        |End.
        |
        |Problem.
        |  f(2)>3
        |End.
      """.stripMargin

    val (d, f) = KeYmaeraXProblemParser.parseProblem(problem("._0"))
    d.decls should have size 1
    d.decls should contain key ("f", None)
    d.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Real
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real), Number(2))
    }
    f shouldBe KeYmaeraXParser("2+2>3")

    val (e, g) = KeYmaeraXProblemParser.parseProblem(problem("."))
    e.decls should have size 1
    e.decls should contain key ("f", None)
    e.decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Real
      codomain shouldBe Real
      interpretation shouldBe Plus(DotTerm(Real), Number(2))
    }
    g shouldBe KeYmaeraXParser("2+2>3")
  }

  it should "parse program definitions" in {
    val problem =
      """
        |Functions.
        |  HP a ::= { x:=*; ?x<=5; ++ x:=y; }.
        |End.
        |
        |ProgramVariables.
        |  R x.
        |  R y.
        |End.
        |
        |Problem.
        |  y<=5 -> [a;]x<=5
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should contain key ("a", None)
    d.decls(("a", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Trafo
      interpretation shouldBe "x:=*; ?x<=5; ++ x:=y;".asProgram
    }
    formula shouldBe "y<=5 -> [x:=*; ?x<=5; ++ x:=y;]x<=5".asFormula
  }

  it should "expand functions and predicates in program definitions" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """
        |Functions.
        |  R f(R) = (.+2).
        |  B p(R,R) <-> (._0<=._1).
        |  HP a ::= { x:=*; ?p(x,5); ++ x:=f(y); }.
        |End.
        |
        |ProgramVariables.
        |  R x.
        |  R y.
        |End.
        |
        |Problem.
        |  y<=5 -> [a;]x<=5
        |End.
      """.stripMargin

    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should contain key ("a", None)
    d.decls(("a", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Trafo
      interpretation shouldBe "x:=*; ?p(x,5); ++ x:=f(y);".asProgram
    }
    formula shouldBe "y<=5 -> [x:=*; ?x<=5; ++ x:=y+2;]x<=5".asFormula
  }

  it should "elaborate in annotations from declarations so far" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """
        |Functions.
        |  B p(R,R) <-> (._0>=._1).
        |  HP loopBody ::= { x:=x+2; }.
        |  HP a ::= { x:=1; {loopBody;}*@invariant(p(x,1)) }.
        |End.
        |
        |ProgramVariables.
        |  R x.
        |End.
        |
        |Problem.
        |  [a;]x>=1
        |End.
      """.stripMargin

    var annotation: Option[(Program, Formula)] = None
    KeYmaeraXParser.setAnnotationListener((prg, fml) => annotation = Some(prg -> fml))
    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should contain key ("a", None)
    d.decls(("a", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Trafo
      interpretation shouldBe "x:=1; {loopBody;}*".asProgram
    }
    d.decls(("loopBody", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Trafo
      interpretation shouldBe "x:=x+2;".asProgram
    }
    annotation shouldBe Some("{x:=x+2;}*".asProgram, "x>=1".asFormula)
    formula shouldBe "[x:=1; {x:=x+2;}*]x>=1".asFormula
  }

  it should "be allowed to ignore later definitions when elaborating annotations" in {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
    val problem =
      """
        |Functions.
        |  HP a ::= { x:=1; {loopBody;}*@invariant(p(x,1)) }.
        |  B p(R,R) <-> (._0>=._1).
        |  HP loopBody ::= { x:=x+2; }.
        |End.
        |
        |ProgramVariables.
        |  R x.
        |End.
        |
        |Problem.
        |  [a;]x>=1
        |End.
      """.stripMargin

    var annotation: Option[(Program, Formula)] = None
    KeYmaeraXParser.setAnnotationListener((prg, fml) => annotation = Some(prg -> fml))
    val (d, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    d.decls should contain key ("a", None)
    d.decls(("a", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Trafo
      interpretation shouldBe "x:=1; {loopBody;}*".asProgram
    }
    d.decls(("loopBody", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Trafo
      interpretation shouldBe "x:=x+2;".asProgram
    }
    annotation shouldBe 'defined
    annotation.get._1 should (be ("{x:=x+2;}*".asProgram) or be ("{loopBody;}*".asProgram))
    annotation.get._2 should (be ("x>=1".asFormula) or be ("p(x,1)".asFormula))
    formula shouldBe "[x:=1; {x:=x+2;}*]x>=1".asFormula
  }
}
