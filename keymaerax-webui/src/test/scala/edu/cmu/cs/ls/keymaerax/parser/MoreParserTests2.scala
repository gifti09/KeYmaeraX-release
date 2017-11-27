package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.immutable._

/** More tests for KeYmaeraXParser
 */
class MoreParserTests2 extends FlatSpec with Matchers with BeforeAndAfterEach {
  val x = Variable("x")
  val y = Variable("y")
  val z = Variable("z")

  val f0 = FuncOf(Function("f",None,Unit,Real),Nothing)
  val g0 = FuncOf(Function("g",None,Unit,Real),Nothing)
  val h0 = FuncOf(Function("h",None,Unit,Real),Nothing)

  val p0 = PredOf(Function("p",None,Unit,Bool),Nothing)
  val q0 = PredOf(Function("q",None,Unit,Bool),Nothing)
  val r0 = PredOf(Function("r",None,Unit,Bool),Nothing)

  val p = Function("p",None,Real,Bool)
  val q = Function("q",None,Real,Bool)
  val r = Function("r",None,Real,Bool)

  var parser: Parser = _
  var pp: PrettyPrinter = _

  override def beforeEach(): Unit = {
    KeYmaeraXTool.init(Map.empty)
    parser = KeYmaeraXParser
    pp = KeYmaeraXPrettyPrinter
  }

  override def afterEach(): Unit = {
    pp = null
    parser = null
    KeYmaeraXTool.shutdown()
  }

  "The parser" should "parse a*(-b-c)" in {
    val input = "a*(-b-c)"

    val parsed = parser(input)

    parsed shouldBe Times(Variable("a"), Minus(Neg(Variable("b")), Variable("c")))
    parsed.prettyString shouldBe input
  }

  it should "parse \\forall x \\forall y \\forall z (x>y & y>z)" in {
    parser("\\forall x \\forall y \\forall z (x>y & y>z)") should be
    Forall(Seq(Variable("x")), Forall(Seq(Variable("y")), Forall(Seq(Variable("z")),
      And(Greater(Variable("x"), Variable("y")), Greater(Variable("y"), Variable("z"))))))
  }

  it should "parse \\forall v (v>=0&true&0>=0->v=v+0*0)<->true" in {
    val v = Variable("v")
    val n0 = Number(0)
    parser("\\forall v (v>=0&true&0>=0->v=v+0*0)<->true") should be
    Equiv(Forall(Seq(v), Imply(And(And(GreaterEqual(v, n0), True), GreaterEqual(n0, n0)), Equal(v, Plus(v, Times(n0, n0))))), True)
  }

  it should "parse (\\forall v (v>=0&true&0>=0->v=v+0*0))<->true" in {
    val v = Variable("v")
    val n0 = Number(0)
    parser("(\\forall v (v>=0&true&0>=0->v=v+0*0))<->true") should be
    Equiv(Forall(Seq(v), Imply(And(And(GreaterEqual(v, n0), True), GreaterEqual(n0, n0)), Equal(v, Plus(v, Times(n0, n0))))), True)
  }

  it should "program parse {x'=5&x>2&x>3} as an ODESystem with one evolution domain constraint" in {
    val x = Variable("x")
    parser.programParser("{x'=5&x>2&x>3}") shouldBe ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
  }

  it should "program parse x'=5&x>2&x>3 as an ODESystem with one evolution domain constraint (if parsed at all)" in {
    val x = Variable("x")
    try {
      parser.programParser("x'=5&x>2&x>3") shouldBe ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
    } catch {
      case _: ParseException => // acceptable
    }
  }

  it should "parse x'=5&x>2&x>3 as an equation system" in {
    val x = Variable("x")
    parser.formulaParser("x'=5&x>2&x>3") shouldBe And(Equal(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
    parser("x'=5&x>2&x>3") shouldBe And(Equal(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
  }

  it should "parse [{x'=5&x>2&x>3}]x>0 as an ODESystem with one evolution domain constraint" in {
    val x = Variable("x")
    parser("[{x'=5&x>2&x>3}]x>0") shouldBe Box(ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3)))), Greater(x, Number(0)))
  }

  it should "parse [{x'=v}]x=0 as a ODESystem with one ODE" in {
    val x = Variable("x")
    parser("[{x'=v}]x=0") shouldBe Box(ODESystem(AtomicODE(DifferentialSymbol(x), Variable("v")), True), Equal(x, Number(0)))
  }

  it should "parse [{x'=v&x<5}]x=0 as a ODESystem with one ODE and evolution domain" in {
    val x = Variable("x")
    parser("[{x'=v&x<5}]x=0") shouldBe Box(ODESystem(AtomicODE(DifferentialSymbol(x), Variable("v")), Less(x, Number(5))), Equal(x, Number(0)))
  }

  it should "parse [{x'=v,v'=a}]x=0 as a ODESystem with two ODEs" in {
    val x = Variable("x")
    parser("[{x'=v,v'=a}]x=0") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), Variable("v")), AtomicODE(DifferentialSymbol(Variable("v")), Variable("a"))), True), Equal(x, Number(0)))
  }

  it should "parse [{x'=v,v'=a&x<5}]x=0 as a ODESystem with two ODEs" in {
    val x = Variable("x")
    parser("[{x'=v,v'=a&x<5}]x=0") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), Variable("v")), AtomicODE(DifferentialSymbol(Variable("v")), Variable("a"))), Less(x,Number(5))), Equal(x, Number(0)))
  }


  it should "program parse {{x'=v}}* as a loopy ODESystem with one ODE" in {
    val x = Variable("x")
    parser.programParser("{{x'=v}}*") shouldBe Loop(ODESystem(AtomicODE(DifferentialSymbol(x), Variable("v")), True))
  }

  it should "parse [{{x'=v}}*]x=0 as a loopy ODESystem with one ODE" in {
    val x = Variable("x")
    parser("[{{x'=v}}*]x=0") shouldBe Box(Loop(ODESystem(AtomicODE(DifferentialSymbol(x), Variable("v")), True)), Equal(x, Number(0)))
  }

  it should "parse [{{x'=v&x<5}}*]x=0 as a loopy ODESystem with one ODE and evolution domain" in {
    val x = Variable("x")
    parser("[{{x'=v&x<5}}*]x=0") shouldBe Box(Loop(ODESystem(AtomicODE(DifferentialSymbol(x), Variable("v")), Less(x, Number(5)))), Equal(x, Number(0)))
  }

  it should "parse [{{x'=v,v'=a}}*]x=0 as a loopy ODESystem with two ODEs" in {
    val x = Variable("x")
    parser("[{{x'=v,v'=a}}*]x=0") shouldBe Box(Loop(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), Variable("v")), AtomicODE(DifferentialSymbol(Variable("v")), Variable("a"))), True)), Equal(x, Number(0)))
  }

  it should "parse [{{x'=v,v'=a&x<5}}*]x=0 as a loopy ODESystem with two ODEs" in {
    val x = Variable("x")
    parser("[{{x'=v,v'=a&x<5}}*]x=0") shouldBe Box(Loop(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), Variable("v")), AtomicODE(DifferentialSymbol(Variable("v")), Variable("a"))), Less(x,Number(5)))), Equal(x, Number(0)))
  }

  it should "refuse ; in ODE-{}" in {
    the [ParseException] thrownBy parser("[{x'=v;v'=2}]x=0") should have message
      """1:7 Unexpected ; in system of ODEs
        |Found:    ; (SEMI$) at 1:7
        |Expected: ,""".stripMargin
  }

  it should "refuse ++ in ODE-{}" in {
    the [ParseException] thrownBy parser("[{x'=v++v'=2}]x=0") should have message
      """1:7 Unexpected ++ in system of ODEs
        |Found:    ++ (CHOICE$) at 1:7 to 1:8
        |Expected: ,""".stripMargin
  }

  it should "refuse ODE 1 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v;]x=0") should have message
      """1:7 ODE without {}
        |Found:    ] (RBOX$) at 1:7
        |Expected: } (RBRACE$)""".stripMargin
  }

  it should "refuse ODE 2 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v & x>0;]x=0") should have message
      """1:13 ODE without {}
        |Found:    ] (RBOX$) at 1:13
        |Expected: } (RBRACE$)""".stripMargin
  }

  it should "refuse ODE systems 1 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v,v'=3;]x=0") should have message
      """1:12 ODE without {}
        |Found:    ] (RBOX$) at 1:12
        |Expected: } (RBRACE$)""".stripMargin
  }

  it should "refuse ODE systems 2 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v,v'=3 & x>0;]x=0") should have message
      """1:18 ODE without {}
        |Found:    ] (RBOX$) at 1:18
        |Expected: } (RBRACE$)""".stripMargin
  }

  it should "parse standalone differential symbols" in {
    parser("x'") shouldBe DifferentialSymbol(Variable("x"))
  }

  it should "parse standalone differentials" in {
    parser("(x')'") shouldBe Differential(DifferentialSymbol(Variable("x")))
  }

  it should "parse terms with differential symbols" in {
    parser("x'=0") shouldBe Equal(DifferentialSymbol(Variable("x")), Number(0))
  }

  it should "parse terms with differentials" in {
    parser("(x')'=0") shouldBe Equal(Differential(DifferentialSymbol(Variable("x"))), Number(0))
  }

  it should "parse postconditions with differential symbols" in {
    parser("<{x'=3}>x'>0") shouldBe Diamond(ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(3)), True),
      Greater(DifferentialSymbol(Variable("x")), Number(0)))
  }

  it should "parse +- in x+-y+1>=5" in {
    parser("x+-y+1>=5") shouldBe GreaterEqual(Plus(Plus(x,Neg(y)),Number(1)), Number(5))
  }

  it should "parse -- in x--y+1>=5" in {
    parser("x--y+1>=5") shouldBe GreaterEqual(Plus(Minus(x,Neg(y)),Number(1)), Number(5))
  }

  it should "term parse f() as f(Nothing)" in {
    parser.termParser("f()") shouldBe FuncOf(Function("f",None,Unit,Real), Nothing)
  }

  it should "term parse f(||) as f(Anything)" in {
    parser.termParser("f(||)") shouldBe UnitFunctional("f", AnyArg, Real)
  }

  it should "formula parse p() as p(Nothing)" in {
    parser.formulaParser("p()") shouldBe PredOf(Function("p",None,Unit,Bool), Nothing)
  }

  it should "formula parse p(||) as p(Anything)" in {
    parser.formulaParser("p(||)") shouldBe UnitPredicational("p", AnyArg)
  }

  it should "round trip term parse f() as f(Nothing)" in {
    parser.termParser(parser.termParser("f()").prettyString) shouldBe FuncOf(Function("f",None,Unit,Real), Nothing)
  }

  it should "round trip term parse f(||) as f(Anything)" in {
    parser.termParser(parser.termParser("f(||)").prettyString) shouldBe UnitFunctional("f", AnyArg, Real)
  }

  it should "round trip formula parse p() as p(Nothing)" in {
    parser.formulaParser(parser.formulaParser("p()").prettyString) shouldBe PredOf(Function("p",None,Unit,Bool), Nothing)
  }

  it should "round trip formula parse p(||) as p(Anything)" in {
    parser.formulaParser(parser.formulaParser("p(||)").prettyString) shouldBe UnitPredicational("p", AnyArg)
  }

  it should "round trip parse dot terms" in {
    parser.termParser(parser.termParser("•").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser(".").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser("•()").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser(".()").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser("•(•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Real))
    parser.termParser(parser.termParser(".(.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Real))
    parser.termParser(parser.termParser("•(•,•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)))
    parser.termParser(parser.termParser(".(.,.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)))
  }

  it should "round trip parse colored dots" in {
    parser.termParser(parser.termParser("•_1").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("._1").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("•_1()").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("._1()").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("•_1(•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Real), Some(1))
    parser.termParser(parser.termParser("._1(.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Real), Some(1))
    parser.termParser(parser.termParser("•_1(•,•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)), Some(1))
    parser.termParser(parser.termParser("._1(.,.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)), Some(1))
  }

  it should "foo" in {
    val t3 = Variable("t", Some(3))
    val B = Variable("B", None)
    val v0 = Variable("v", Some(0))
    parser("-(1)*(v_0+-B*t_3--B/2*t_3)+-t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))") should be
    Plus(
      Times(Neg(Number(1)), Plus(v0, Minus(Times(Neg(B), t3), Times(Divide(Neg(B), Number(2)), t3)))),
      Neg(Times(t3, Minus(Neg(B), Plus(Times(Divide(Minus(Times(Number(0), Number(2)), Times(Neg(B), Number(0))), Power(Number(2), Number(2))), t3), Times(Divide(B, Number(2)), Number(1)))))))
  }

  it should "bar" in {
    val t3 = Variable("t", Some(3))
    val B = Variable("B", None)
    parser("t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))") should be
    Times(t3, Minus(Neg(B), Plus(Times(Divide(Minus(Times(Number(0), Number(2)), Times(Neg(B), Number(0))), Power(Number(2), Number(2))), t3), Times(Divide(Neg(B), Number(2)), Number(1)))))
  }

  it should "baz" in {
    val t3 = Variable("t", Some(3))
    val B = Variable("B", None)
    val v0 = Variable("v", Some(0))
    val dx0 = Variable("dx", Some(0))
    parser("\\forall V \\forall dx_0 \\forall B \\forall dy_0 \\forall dx \\forall v \\forall yo_0 \\forall x_0 \\forall y_0 \\forall v_0 \\forall r \\forall xo_0 \\forall dy \\forall A \\forall t_3 (v_0+-B*t_3)*dx_0-0 <= 1*(v_0+-B*t_3--B/2*t_3) + t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))") should be
    Forall(Seq(Variable("V")),
      Forall(Seq(Variable("dx", Some(0))),
        Forall(Seq(Variable("B")),
          Forall(Seq(Variable("dy", Some(0))),
            Forall(Seq(Variable("dx")),
              Forall(Seq(Variable("v")),
                Forall(Seq(Variable("yo", Some(0))),
                  Forall(Seq(Variable("x", Some(0))),
                    Forall(Seq(Variable("y", Some(0))),
                      Forall(Seq(Variable("v", Some(0))),
                        Forall(Seq(Variable("r")),
                          Forall(Seq(Variable("xo", Some(0))),
                            Forall(Seq(Variable("dy")),
                              Forall(Seq(Variable("A")),
                                Forall(Seq(Variable("t", Some(3))),
                                  LessEqual(
                                    Minus(Times(Plus(v0, Times(Neg(B), t3)), dx0), Number(0)),
                                    Plus(
                                      Times(Number(1), Plus(v0, Minus(Times(Neg(B), t3), Times(Divide(Neg(B), Number(2)), t3)))),
                                      Times(t3, Minus(Neg(B), Plus(Times(Divide(Minus(Times(Number(0), Number(2)), Times(Neg(B), Number(0))), Power(Number(2), Number(2))), t3), Times(Divide(Neg(B), Number(2)), Number(1))))))
                                  )
                                )))))))))))))))
  }

  it should "parse a long chain of quantifiers" in {
    val parsed = parser("\\forall V \\forall dx_0 \\forall B \\forall dy_0 \\forall dx \\forall v \\forall yo_0 \\forall x_0 \\forall y_0 \\forall v_0 \\forall r \\forall xo_0 \\forall dy \\forall A \\forall t_3 (ep()>0&V>=0&B>0&A>=0&r!=0&v>=0&(v_0=0|(x_0-xo_0>=0->x_0-xo_0>v_0^2/(2*B)+V*(v_0/B))&(x_0-xo_0<=0->xo_0-x_0>v_0^2/(2*B)+V*(v_0/B))|(y_0-yo_0>=0->y_0-yo_0>v_0^2/(2*B)+V*(v_0/B))&(y_0-yo_0<=0->yo_0-y_0>v_0^2/(2*B)+V*(v_0/B)))&r_0()!=0&v_0>=0&dx^2+dy^2=1&dxo()^2+dyo()^2<=V^2&x0_1()=x_0&dx^2+dy^2=1&v_0>=0&dx_0^2+dy_0^2=1&t_3>=0&t_3<=ep()&0>=0&0<=ep()&v_0=v_0+-B*0&v_0+-B*t_3>=0->-(1)*(v_0+-B*t_3--B/2*t_3)+-t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))<=(v_0+-B*t_3)*dx_0-0&(v_0+-B*t_3)*dx_0-0<=1*(v_0+-B*t_3--B/2*t_3)+t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1)))<->true")
    println("Parsed: " + parsed.prettyString)
    parsed.prettyString shouldBe "\\forall V \\forall dx_0 \\forall B \\forall dy_0 \\forall dx \\forall v \\forall yo_0 \\forall x_0 \\forall y_0 \\forall v_0 \\forall r \\forall xo_0 \\forall dy \\forall A \\forall t_3 (ep()>0&V>=0&B>0&A>=0&r!=0&v>=0&(v_0=0|(x_0-xo_0>=0->x_0-xo_0>v_0^2/(2*B)+V*(v_0/B))&(x_0-xo_0<=0->xo_0-x_0>v_0^2/(2*B)+V*(v_0/B))|(y_0-yo_0>=0->y_0-yo_0>v_0^2/(2*B)+V*(v_0/B))&(y_0-yo_0<=0->yo_0-y_0>v_0^2/(2*B)+V*(v_0/B)))&r_0()!=0&v_0>=0&dx^2+dy^2=1&dxo()^2+dyo()^2<=V^2&x0_1()=x_0&dx^2+dy^2=1&v_0>=0&dx_0^2+dy_0^2=1&t_3>=0&t_3<=ep()&0>=0&0<=ep()&v_0=v_0+-B*0&v_0+-B*t_3>=0->- 1*(v_0+-B*t_3--B/2*t_3)+-t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))<=(v_0+-B*t_3)*dx_0-0&(v_0+-B*t_3)*dx_0-0<=1*(v_0+-B*t_3--B/2*t_3)+t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1)))<->true"
  }


  "Parsing state-dependents" should "parse (||) AnyArg" in {
    parser("x>2&p(||)") shouldBe And(Greater(Variable("x"),Number(2)), UnitPredicational("p",AnyArg))
    parser.formulaParser("p(||)") shouldBe UnitPredicational("p",AnyArg)
    parser("5<=f(||)") shouldBe LessEqual(Number(5),UnitFunctional("f",AnyArg,Real))
    parser.termParser("f(||)") shouldBe UnitFunctional("f",AnyArg,Real)
  }

  it should "parse (|x|) Exception taboos" in {
    parser("x>2&p(|x|)") shouldBe And(Greater(Variable("x"),Number(2)), UnitPredicational("p",Except(Variable("x"))))
    parser.formulaParser("p(|x|)") shouldBe UnitPredicational("p",Except(Variable("x")))
    parser("5<=f(|x|)") shouldBe LessEqual(Number(5),UnitFunctional("f",Except(Variable("x")),Real))
    parser.termParser("f(|x|)") shouldBe UnitFunctional("f",Except(Variable("x")),Real)
    parser("[{x'=5,c{|x|}}]x>2") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("x")),Number(5)),
      DifferentialProgramConst("c",Except(Variable("x")))), True),
      Greater(Variable("x"),Number(2)))
    parser("[{z'=5,d{|y|}}]x>2") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("z")),Number(5)),
      DifferentialProgramConst("d",Except(Variable("y")))), True),
      Greater(Variable("x"),Number(2)))
    parser("<{x'=5,c{|x|}}>x>2") shouldBe Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("x")),Number(5)),
      DifferentialProgramConst("c",Except(Variable("x")))), True),
      Greater(Variable("x"),Number(2)))
    parser("<{z'=5,d{|y|}}>x>2") shouldBe Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("z")),Number(5)),
      DifferentialProgramConst("d",Except(Variable("y")))), True),
      Greater(Variable("x"),Number(2)))
  }

  it should "parse DG snippets" in {
    parser("[{x'=2,c{|y_|}}]x=99") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("x")),Number(2)), DifferentialProgramConst("c",Except(Variable("y_")))), True), Equal(Variable("x"),Number(99)))
    parser("[{c{|y_|}}]x=99") shouldBe Box(ODESystem(DifferentialProgramConst("c",Except(Variable("y_"))), True), Equal(Variable("x"),Number(99)))
    parser("[{c{|y_|}}]p(|y_|)") shouldBe Box(ODESystem(DifferentialProgramConst("c",Except(Variable("y_"))), True), UnitPredicational("p",Except(Variable("y_"))))
    parser("[{c{|y_|}&H(|y_|)}]p(|y_|)") shouldBe Box(ODESystem(DifferentialProgramConst("c",Except(Variable("y_"))), UnitPredicational("H",Except(Variable("y_")))), UnitPredicational("p",Except(Variable("y_"))))

  }
}
