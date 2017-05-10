package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Created by yongkiat on 11/27/16.
  */
class PolynomialArithTests extends TacticTestBase {

  "PolynomialArith" should "order variables" in withMathematica { qeTool =>
    val vars = List("x","z","x()","z()","a+b","c+d").map(_.asTerm)

    vars.combinations(2).toList.map{ case List(x,y) => {VarOrd.compare(x,y)}} shouldBe List(-2,-1,-1,0,0,-1,-1,0,0,-2,0,0,0,0,0)
    vars.combinations(2).toList.map{ case List(x,y) => {VarOrd.compare(y,x)}} shouldBe List(2,1,1,0,0,1,1,0,0,2,0,0,0,0,0)
  }

  "PolynomialArith" should "check monomial normalization" in withMathematica { qeTool =>
    //Note: recently changed to reverse lexicographic
    val m1 = "1 * a^5 * x^5".asTerm //Valid
    val m2 = "1 * x^5 * x()^5".asTerm //Valid
    val m3 = "1 * y^5 * x^5".asTerm //Invalid
    val m4 = "1 * (a^5 * x^5)".asTerm //Invalid
    val m5 = "1 * b^1 * x^7 * z()^8".asTerm //Valid
    val m6 = "1 * a^8 * x^7 * z()^1".asTerm //Valid
    (checkMono(m1),checkMono(m2),checkMono(m3),checkMono(m4),checkMono(m5),checkMono(m6)) shouldBe
       (true,true,false,false,true,true)
  }


  "PolynomialArith" should "check monomial ordering" in withMathematica { qeTool =>
    val m1 = "1 * a^5 * x^5".asTerm //Valid
    val m2 = "1 * x^5 * x()^5".asTerm //Valid
    val m5 = "1 * b^1 * x^7 * z()^8".asTerm //Valid
    val m6 = "1 * a^8 * x^7 * z()^1".asTerm //Valid
    val m7 = "1 * a^8 * x^7 * z()^1".asTerm //Valid

    val vars = List(m1,m2,m5,m6,m7)

    (vars.combinations(2).toList.map{ case List(x,y) => {MonOrd.compare(x,y)}}) shouldBe List(-1,-1,-1,-1,-1,1,0)
    (vars.combinations(2).toList.map{ case List(x,y) => {MonOrd.compare(y,x)}}) shouldBe List(1,1,1,1,1,-1,0)

  }

  "PolynomialArith" should "check polynomial normalization" in withMathematica { qeTool =>
    val p1 = "0 + 5/7 * (1 * a^5 * x^5) + 5/8 * (1 * b^5 * x^5)".asTerm //Valid
    val p2 = "0 + 5/1 * (1 * a^5 * c^5) + -5/1 * (1 * a^5 * x^5)".asTerm //Valid
    val p3 = "0 + 5 * (1 * a^5 * x^6) + 5 * (1 * a^5 * x^5)".asTerm //Invalid (ordering)
    val p4 = "0 + 5/2 * (1 * a^6 * x^5) + 5/3 * (1 * a^5 * x^6)".asTerm //Valid
    val p5 = "0 + -11/2 * (1 * a^6 * x^5) + 5/-3 * (1 * a^5 * x^6)".asTerm //Invalid (negative denominator)
    val p6 = "0 + -11/11 * (1 * a^6 * x^5) + 5/5 * (1 * a^5 * x^6)".asTerm //Invalid (GCD)

    (checkPoly(p1), checkPoly(p2), checkPoly(p3),
     checkPoly(p4), checkPoly(p5), checkPoly(p6)) shouldBe(true,true,false,true,false,false)
  }

  "PolynomialArith" should "do poly add" in withMathematica { qeTool =>
    val p1 = "0 + 5/7 * (1 * a^5 * x^5) + 5/8 * (1 * b^5 * x^5)".asTerm //Valid
    val p2 = "0 + 5/1 * (1 * a^5 * c^5) + -5/1 * (1 * a^5 * x^5)".asTerm //Valid
    val p3 = "0 + 5/2 * (1 * a^6 * x^5) + 5/3 * (1 * a^5 * x^6)".asTerm //Valid

    val (p4,r4) = addPoly(p1,p2)
    val (p5,r5) = addPoly(p4,p3)
    val (p6,r6) = addPoly(p5,p5)

    println(p4,p5,p6)
    (checkPoly(p4),checkPoly(p5),checkPoly(p6)) shouldBe (true,true,true)
    //(r4.isProved,r5.isProved,r6.isProved) shouldBe (true,true,true)
  }

  "PolynomialArith" should "do mono mul" in withMathematica { qeTool =>
    val m1 = "1 * a^5 * x^5".asTerm
    val m2 = "1 * b^1 * x^7 * z^8".asTerm
    val m3 = "1 * x^8 * z^7 * a()^1".asTerm

    val p1 = "0 + 5/11 * (1 * x^5 * a()^5) + 5/3 * (1 * x^5 * b()^5)".asTerm

    val (m4,r4) = mulMono(m1,m2)
    val (m5,r5) = mulMono(m4,m3)
    val (m6,r6) = mulMono(m5,m5)

    val (p2,r2) = mulPolyMono(p1,Divide(Number(3),Number(5)),m4)

    //println(m4,m5,m6)
    (checkPoly(p1),checkPoly(p2)) shouldBe (true,true)
  }

  "PolynomialArith" should "do poly mul" in withMathematica { qeTool =>
    val p1 = "0 + 1/5 * (1 * x^2) + 5/1 * (1 * a()^2)".asTerm
    val p2 = "0 + 5/3 * (1 * y^1) + -1/5 * (1 * a()^2)".asTerm

    val (p3,r3) = addPoly(p1,p2)
    val (p4,r4) = mulPoly(p1,p2)
    val (p5,r5) = mulPoly(p3,p4)

    //println(p4)
    //println(p5)
    (checkPoly(p1),checkPoly(p2),checkPoly(p3),checkPoly(p4),checkPoly(p5)) shouldBe (true,true,true,true,true)
  }

  "PolynomialArith" should "do poly add with proof" in withMathematica { qeTool =>
    val p1 = "0 + 2/3 * (1 * x^ 1) + 2/5 * (1 * b()^2)".asTerm
    val p2 = "0 + -2/3 * (1 * x^1) + 2/5 * (1 * a()^2)".asTerm

    val (p3,r3) = addPoly(p1,p2) //Cancelling coefficients
    val (p4,r4) = addPoly(p1,p1) //Adding coefficients
    val (p5,r5) = addPoly(p2,p1) //Inverse

    p3 shouldBe "0+2/5*(1*a()^2)+2/5*(1*b()^2)".asTerm
    p4 shouldBe "0+4/3*(1*x^1)+4/5*(1*b()^2)".asTerm
    p5 shouldBe "0+2/5*(1*a()^2)+2/5*(1*b()^2)".asTerm

    r3 shouldBe 'proved
    r4 shouldBe 'proved
    r5 shouldBe 'proved
  }

  "PolynomialArith" should "do mono mul with proof" in withMathematica { qeTool =>
    //Note: ^-1 isn't actually allowed
    val m1 = "(1 * y^ 1 * x()^2)".asTerm
    val m2 = "1* y^-1 * a()^2 ".asTerm

    val (m3,r3) = mulMono(m1,m2) //Cancelling coefficients
    val (m4,r4) = mulMono(m1,m1) //Adding coefficients
    val (m5,r5) = mulMono(m2,m1) //Inverse

    m3 shouldBe "1*a()^2*x()^2".asTerm
    m4 shouldBe "1*y^2*x()^4".asTerm
    m5 shouldBe "1*a()^2*x()^2".asTerm

    r3 shouldBe 'proved
    r4 shouldBe 'proved
    r5 shouldBe 'proved
  }

  "PolynomialArith" should "do poly mono mul with proof" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a()^5".asTerm
    val p1 = "0 + 5/2 * (1 * x^2) + 5/2 * (1 * y()^2)".asTerm
    val (p2,r2) = mulPolyMono(p1,Divide(Number(2),Number(5)),m1)

    p2 shouldBe "0+1/1*(1*x^7*a()^5)+1/1*(1*x^5*a()^5*y()^2)".asTerm
    r2 shouldBe 'proved
  }

  "PolynomialArith" should "do poly mul with proof" in withMathematica { qeTool =>
    val p1 = "0 + 1/5 * (1 * x^2) + 1/3 * (1 * a()^2)".asTerm
    val p2 = "0 + 5/2 * (1 * y^1) + 4/1 * (1 * a()^2)".asTerm

    val (p3,r3) = addPoly(p1,p2)
    val (p4,r4) = mulPoly(p1,p2)
    val (p5,r5) = mulPoly(p3,p4)

    p4 shouldBe "0+1/2*(1*x^2*y^1)+5/6*(1*y^1*a()^2)+4/5*(1*x^2*a()^2)+4/3*(1*a()^4)".asTerm
    p5 shouldBe "0+5/4*(1*x^2*y^2)+25/12*(1*y^2*a()^2)+1/10*(1*x^4*y^1)+13/3*(1*x^2*y^1*a()^2)+125/18*(1*y^1*a()^4)+4/25*(1*x^4*a()^2)+56/15*(1*x^2*a()^4)+52/9*(1*a()^6)".asTerm

    r4 shouldBe 'proved
    r5 shouldBe 'proved
  }

  "PolynomialArith" should "do iterated squares with proof" in withMathematica { qeTool =>

    val (t1,r1) = iterSquare("(x+yz+k)".asTerm,3)
    val (t2,r2) = iterSquare("(x+z+y)".asTerm,9)
    val (t3,r3) = iterSquare("(xyz+yzx)".asTerm,12)

    t1 shouldBe "(x+yz+k)^2*(x+yz+k)".asTerm
    t2 shouldBe "(((x+z+y)^2)^2)^2*(x+z+y)".asTerm
    t3 shouldBe "(((xyz+yzx)^2*(xyz+yzx))^2)^2".asTerm

    r1 shouldBe 'proved
    r2 shouldBe 'proved
    r3 shouldBe 'proved
  }

  "PolynomialArith" should "do poly normalize with proof" in withMathematica { qeTool =>
    val p1 = "x * x + y + z * 5".asTerm
    val p2 = "y*(z + z + x ) * (x* y)".asTerm
    val p3 = "- (x^2 + y^2*z)".asTerm
    val p4 = "x^2 - (x^2 + y^2*z)".asTerm
    val p5 = "(x+y*z -x - y*z + a)^3".asTerm
    val p6 = "1+(a*b*c)^2-(x-y-1*a^2)*(0+-1*(1*y^1*c^2*b^2))".asTerm

    val (t1,r1) = normalise(p1)
    val (t2,r2) = normalise(p2)
    val (t3,r3) = normalise(p3)
    val (t4,r4) = normalise(p4)
    val (t5,r5) = normalise(p5)
    val (t6,r6) = normalise(p6)

    println(t1,t2,t3,t4,t5,t6)
    (checkPoly(t1),checkPoly(t2),checkPoly(t3),checkPoly(t4),checkPoly(t5),checkPoly(t6)) shouldBe (true,true,true,true,true,true)
    r1 shouldBe 'proved
    r2 shouldBe 'proved
    r3 shouldBe 'proved
    r4 shouldBe 'proved
    r5 shouldBe 'proved
    r6 shouldBe 'proved
  }

  "PolynomialArith" should "do mono div" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a()^5".asTerm
    val m2 = "1 * x^1 * z^7 * b()^8".asTerm
    val m3 = "1 * z^8 * a()^7 * x()^1".asTerm
    val m4 = "1 * z^5 * x()^1".asTerm

    println(divMono(m2,m1)) //Not Divisible
    println(divMono(m2,m2)) //Divisible
    println(divMono(m3,m2)) //Not Divisible
    println(divMono(m3,m4)) //Divisible

  }

  "PolynomialArith" should "do poly div" in withMathematica { qeTool =>
    val p1 = normalise("x - y -1*a^2".asTerm)._1
    val p2 = normalise("z-b^2".asTerm)._1
    val p3 = normalise("z*(y-x)*c^2-1".asTerm)._1
    val p = normalise("1+(a*b*c)^2".asTerm)._1

    println(reduction(List(p1,p2,p3),p))
  }

  "PolynomialArith" should "normalize pure arithmetic sequent" in withMathematica { qeTool =>
    // A sequent of pure arithmetic only has (in)equational formulas (operators >,>=,=  TODO: !=)
    // i.e. no dL, no &, |, <, <= negations, etc.
    val antes = IndexedSeq(
      "x + y + z >= F() + G()".asFormula,
      "k * z > a + b".asFormula,
      "c - d > z".asFormula,
      "d * f = 12".asFormula
    )
    val succs = IndexedSeq(
      "k >= z".asFormula,
      "k+b = z+y+a".asFormula,
      "c > d".asFormula,
      "g() >= f()".asFormula,
      "K() = A+B+C".asFormula
    )
    val pr = proveBy(Sequent(antes,succs),prepareArith)

    pr.subgoals should contain only
      Sequent(IndexedSeq("d*f-12=0","(z-k)*wit__0^2-1=0","(z+y+a-(k+b))*wit__1-1=0","d-c-wit__2^2=0","(f()-g())*wit__3^2-1=0","(A+B+C-K())*wit__4-1=0","(c-d-z)*wit__5^2-1=0","(k*z-(a+b))*wit__6^2-1=0","x+y+z-(F()+G())-wit_^2=0").map(_.asFormula),
        IndexedSeq())
  }

  "PolynomialArith" should "rewrite equality to desired shape in arbitrary positions" in withMathematica { qeTool =>
    val antes = IndexedSeq(
      "a + b = c".asFormula,
      "x + 2/5*y + z = F() + G()".asFormula,
      "d * f = 12 & 2 * a -5 + 2 * c= b".asFormula
    )
    val succs = IndexedSeq(
      "k = z".asFormula,
      "g() = f()".asFormula,
      "K() = A+2*B+C".asFormula
    )

    val rewrites = List(
      (SuccPosition(1),"z".asTerm,"k".asTerm,"-1".asTerm),
      (AntePosition(2),"y".asTerm,"5/2*(F()+G()-x-z)".asTerm,"2/5".asTerm),
      (AntePosition(3,1::Nil),"a".asTerm,"b/2+5/2-c".asTerm,"2".asTerm)
    )
    val elim = (rewriteEquality _).tupled
    val pr = proveBy(Sequent(antes,succs), rewrites.foldLeft(nil)(_ & elim(_)))
    pr.subgoals should contain only
      Sequent(IndexedSeq("a+b=c","y=5/2*(F()+G()-x-z)","d*f=12&a=b/2+5/2-c").map(_.asFormula),
              IndexedSeq("z=k","g()=f()","K()=A+2*B+C").map(_.asFormula))
  }

  "PolynomialArith" should "generate generalised non-zero squares witness" in withMathematica { qeTool =>
    val witness = List("x+y+z ".asTerm,"z-b^2".asTerm,"a-b^2*c".asTerm).map( t => (Number(5),t))
    val gtz = "a+b*c*d".asTerm
    val pr = genWitness(gtz,witness)
    pr._1 shouldBe "a+b*c*d+(0+5*(a-b^2*c)^2+5*(z-b^2)^2+5*(x+y+z)^2)".asTerm
    pr._2 shouldBe 'proved
    pr._2.conclusion.succ(0) shouldBe "a+b*c*d>0->a+b*c*d+(0+5*(a-b^2*c)^2+5*(z-b^2)^2+5*(x+y+z)^2)>0".asFormula
  }

  "PolynomialArith" should "prove JH's example using special case witness (g=1)" in withMathematica { qeTool =>

    //One direction of the quadratic formula (non-zeroness of determinants)
    val antes = IndexedSeq("a*x^2 + b*x + c=0").map(_.asFormula)
    val succ = IndexedSeq("b^2-4*a*c >= 0").map(_.asFormula)

    val ineq = List()
    val linear = List((0,"c","-a*x^2 - b*x","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("4","a*wit_*x + 1/2*b*wit_")).map( s => (s._1.asTerm,s._2.asTerm))
    val insts = List((0,"1")).map (s => (s._1,s._2.asTerm))

    //For this problem, the ante/succ pair is already a groebner basis in degrevlex ordering
    val res = proveBy(Sequent(antes,succ),prepareArith & printGoal & linearElim(linear) & genWitnessTac(ineq,witness))
    //Alternatively, we can compute the cofactors
    val res2 = proveBy(Sequent(antes,succ),prepareArith & linearElim(linear) & genWitnessTac(ineq,witness,Some(insts)))

    res shouldBe 'proved
    res2 shouldBe 'proved
  }

  "PolynomialArith" should "prove more JH examples (1)" in withMathematica { qeTool =>

    val antes = IndexedSeq("0<=a","0<=b","0<=c","c*(2*a+b)^3/27 <= x").map(_.asFormula)
    val succ = IndexedSeq("c*a^2*b <=x").map(_.asFormula)
    val ineq = List(0)
    val linear = List((4,"a","wit_^2","-1"),(3,"b","wit__3^2","-1"),(2,"c","wit__2^2","-1"),(0,"x","wit_^4*wit__2^2*wit__3^2 - wit__0^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("8/27","wit_^3*wit__0*wit__2 - wit_*wit__0*wit__2*wit__3^2"),("1/27","-wit_^2*wit__0*wit__2*wit__3 + wit__0*wit__2*wit__3^3"),("1","wit__0*wit__1")).map( s => (s._1.asTerm,s._2.asTerm))

    //For this problem, the ante/succ pair is already a groebner basis in degrevlex ordering
    val res = proveBy(Sequent(antes,succ),prepareArith2 & printGoal& linearElim(linear) & genWitnessTac(ineq,witness))

    res shouldBe 'proved
  }

  "PolynomialArith" should "prove more JH examples (2)" in withMathematica { qeTool =>

    val antes = IndexedSeq("1<=t","t<=1").map(_.asFormula)
    val succ = IndexedSeq("0<=1+r^2-2*r*t").map(_.asFormula)
    val ineq = List(0)
    val linear = List((1,"t","-wit__1^2 + 1","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("1","-r*wit__0 + wit__0"),("1/2","-r*wit_ + wit__0^2*wit_"),("1/2","r*wit__1 + wit__0^2*wit__1")).map( s => (s._1.asTerm,s._2.asTerm))
    val insts = Some(List((0,"-2*r*wit_^2 + r^2 - 2*r + 1"),(1,"-1/2*wit__0^4 - 4*r^2*wit__1^2 - 2*r^3 - r*wit__0^2 + 7/2*r^2 - 2*r")).map (s => (s._1,s._2.asTerm)))

    val res = proveBy(Sequent(antes,succ),prepareArith2 & printGoal& linearElim(linear) & genWitnessTac(ineq,witness,insts))
    res shouldBe 'proved
  }

  "PolynomialArith" should "prove more JH examples (3)" in withMathematica { qeTool =>

    val antes = IndexedSeq("a*a+a*b-b*b>=0","2*a+b>=0","c*c+c*d-d*d<=0","d>=0").map(_.asFormula)
    val succ = IndexedSeq("a*d+c*b+b*d>=0").map(_.asFormula)
    val ineq = List(0)
    val linear = List((3,"a","1/2*wit__3^2 - 1/2*b","2"),(1,"d","wit__1^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("1","wit__0*wit__1*wit__3"),("1/5","wit__3^2*wit__2"),("1/5","2*c*wit_ + wit__1^2*wit_")).map( s => (s._1.asTerm,s._2.asTerm))
    val insts = Some(List((0,"wit__1^2*wit__3^2"),(1,"-1/5*wit__3^4"),(2,"1/5*wit__1^4 + 4/5*c*wit__1^2 + 4/5*c^2")).map (s => (s._1,s._2.asTerm)))
    val res = proveBy(Sequent(antes,succ),prepareArith2 & printGoal& linearElim(linear) & genWitnessTac(ineq,witness,insts))
    res shouldBe 'proved
  }

  "PolynomialArith" should "prove more JH examples (4)" in withMathematica { qeTool =>
    //Same as (3), but >= changed to >, Harrison reports that this is harder for his implementation
    val antes = IndexedSeq("a*a+a*b-b*b>0","2*a+b>0","c*c+c*d-d*d<=0","d>0").map(_.asFormula)
    val succ = IndexedSeq("a*d+c*b+b*d>=0").map(_.asFormula)
    val ineq = List(0)
    val linear = List((2,"a","1/2*wit__2^2 - 1/2*b","2"),(1,"d","wit__1^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("1","wit__0*wit__1*wit__2"),("1/5","wit__2^2*wit_"),("1/5","2*c*wit__3 + wit__1^2*wit__3")).map( s => (s._1.asTerm,s._2.asTerm))
    val insts = Some(List((0,"wit__1^2*wit__2^2"),(1,"1/5*wit__1^4 + 4/5*c*wit__1^2 + 4/5*c^2"),(2,"-1/5*wit__2^4")).map (s => (s._1,s._2.asTerm)))
    val res = proveBy(Sequent(antes,succ),prepareArith2 & printGoal& linearElim(linear) & genWitnessTac(ineq,witness,insts))
    res shouldBe 'proved
  }

  "PolynomialArith" should "prove RWV example with general oracle witness" in withMathematica { qeTool =>
    val antes = IndexedSeq("x - y -1*a^2","z-b^2","z*(y-x)*c^2-1").map(t => Equal(t.asTerm,Number(0)))

    val seq = Sequent(antes,IndexedSeq())
    //The witness is 1+ 1*(a*b*c)^2
    val w = ("1".asTerm,"(a*b*c)".asTerm)

    val insts = List((1,"a^2*c^2".asTerm),(0,"z*c^2".asTerm),(2,"1".asTerm))

    //Guided reduction
    val pr1 = proveBy(seq,genWitnessTac(List(),List(w),Some(insts)))

    //Since the input happens to be a groebner basis, we can use confluent automated reduction
    val pr2 = proveBy(seq,genWitnessTac(List(),List(w)))
    val pr3 = proveBy(seq,genWitnessTac(List(),List(w)))
    val pr4 = proveBy(seq,genWitnessTac(List(),List(w)))

    pr1 shouldBe 'proved
    pr2 shouldBe 'proved
    pr3 shouldBe 'proved
    pr4 shouldBe 'proved
  }

  "PolynomialArith" should "prove non-negativity of the Motzkin polynomial" in withMathematica { qeTool =>
    //Standard example used in many SOS papers
    val antes = IndexedSeq()
    val succ = IndexedSeq("x1^6+x2^4*x3^2+x2^2*x3^4-3*x1^2*x2^2*x3^2>=0").map(_.asFormula)
    val ineq = List(0)
    val witness = List(("1","wit_*x1^3"),("1","-9/14*wit_*x1^2*x3 + wit_*x2^2*x3"),("1","-9/14*wit_*x1^2*x2 + wit_*x2*x3^2"),("3/7","x1^4*x2*x3 - 1/2*x1^2*x2^3*x3 - 1/2*x1^2*x2*x3^3"),("3/7","-x1^5*x2 + x1*x2^3*x3^2"),("3/7","-x1^5*x3 + x1*x2^2*x3^3"),("9/28","-x1^2*x2^3*x3 + x1^2*x2*x3^3"),("3/196","wit_*x1^2*x3"),("3/196","wit_*x1^2*x2")).map( s => (s._1.asTerm,s._2.asTerm))

    val res = proveBy(Sequent(antes,succ),prepareArith2 & printGoal& genWitnessTac(ineq,witness))
    res shouldBe 'proved
  }

  "PolynomialArith" should "prove JH examples from Monniaux & Corbineau, ITP'11" in withMathematica { qeTool =>
    val problems = List(
      Sequent(IndexedSeq("0<=x","0<=y","0<=z","x*y*z=1").map(_.asFormula),IndexedSeq("x+y+z <= (x^2 * z + y^2 * x + z^2 * y)").map(_.asFormula)),
      //The positive squares heuristic doesn't work for this one
      //Sequent(IndexedSeq("0<=x","0<=y","0<=z").map(_.asFormula),IndexedSeq("(x^2 * z + y^2 * x + z^2 * y)^3 <= ((x * y * z)^2 * (x + y + z)^3)").map(_.asFormula)),
      Sequent(IndexedSeq("(a^2 = (k^2 + 1) * b^2)","1<=k","1<=a","1<=b").map(_.asFormula),IndexedSeq("(a - k * b) < b").map(_.asFormula))
    )
    val ineq = List(0)
    val witness = List(("1","wit_*x1^3"),("1","-9/14*wit_*x1^2*x3 + wit_*x2^2*x3"),("1","-9/14*wit_*x1^2*x2 + wit_*x2*x3^2"),("3/7","x1^4*x2*x3 - 1/2*x1^2*x2^3*x3 - 1/2*x1^2*x2*x3^3"),("3/7","-x1^5*x2 + x1*x2^3*x3^2"),("3/7","-x1^5*x3 + x1*x2^2*x3^3"),("9/28","-x1^2*x2^3*x3 + x1^2*x2*x3^3"),("3/196","wit_*x1^2*x3"),("3/196","wit_*x1^2*x2")).map( s => (s._1.asTerm,s._2.asTerm))

    val res = problems.map( s => proveBy(s,prepareArith2 & printGoal)) //& genWitnessTac(ineq,witness))

  }

  "PolynomialArith" should "remove division from antecedents" in withMathematica { qeTool =>
    val antes = IndexedSeq("x/y + a/b + c * d","a+b*c/2","5","X() +A()+B()/C()").map(t => Equal(t.asTerm,Number(0)))
    val seq = Sequent(antes,IndexedSeq())
    println(proveBy(seq,ratFormTac(0,true,true)))
    println(proveBy(seq,ratFormTac(0,true,false)))
  }

  "PolynomialArith" should "normalise sequent without changing structure" in withMathematica { qeTool =>
    val antes = IndexedSeq(
      "a + b = c | (d <= 0 & c = 5)".asFormula,
      "x + 2/5*y >=z & F() < G()".asFormula,
      "d * f = 12 & 2 * a -5 + 2 * c= b".asFormula
    )
    val succs = IndexedSeq(
      "k = z".asFormula,
      "g() <= f()".asFormula,
      "K() > A+2*B+C & A<=B+C*D | E=0".asFormula
    )

    val pr = proveBy(Sequent(antes,succs), normaliseNNF)
    println(pr)

  }
}
