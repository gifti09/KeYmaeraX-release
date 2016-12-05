package cbcps

import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.bellerophon.{RenUSubst, _}
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core.{And, NamedSymbol, StaticSemantics, SuccPos, _}
import edu.cmu.cs.ls.keymaerax.launcher.{DefaultConfiguration}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool, ToolEvidence}
import edu.cmu.cs.ls.keymaerax.tools._
import Utility._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics.{implyRi, andLi => _, modusPonens => _, _}
import edu.cmu.cs.ls.keymaerax.btactics._
import sun.security.provider.certpath.IndexedCollectionCertStore

import scala.collection.immutable._
import scala.collection.immutable.Nil
import scala.collection.{immutable, mutable}
import scala.util.Try


object Utility {

  def v(f: Expression): Seq[Variable] =
    if (f == null)
      return Seq.empty[Variable]
    else
      StaticSemantics.vars(f).toSet[NamedSymbol].toSeq.map(v => v match {
        case v: Variable => v
        case d: DifferentialSymbol => d.x
        case x => require(false, "Unknown NamedSymbol: " + x); null
      })(collection.breakOut)

  def fv(f: Expression): Seq[Variable] =
    if (f == null)
      return Seq.empty[Variable]
    else
      StaticSemantics.freeVars(f).toSet[NamedSymbol].toSeq.map(v => v match {
        case v: Variable => v
        case d: DifferentialSymbol => d.x
        case x => println("Unknown NamedSymbol: " + x); null
      })(collection.breakOut)

  def bv(f: Formula): Seq[Variable] =
    if (f == null)
      return Seq.empty[Variable]
    else
      StaticSemantics.boundVars(f).toSet[NamedSymbol].toSeq.map(v => v match {
        case v: Variable => v
        case d: DifferentialSymbol => d.x
        case x => println("Unknown NamedSymbol: " + x); null
      })(collection.breakOut)

  def bv(f: Program): Seq[Variable] =
    if (f == null)
      return Seq.empty[Variable]
    else
      StaticSemantics.boundVars(f).toSet[NamedSymbol].toSeq.map(v => v match {
        case v: Variable => v
        case d: DifferentialSymbol => d.x
        case x => println("Unknown NamedSymbol: " + x); null
      })(collection.breakOut)

  def loadLemma(id: LemmaID): Option[Lemma] = LemmaDBFactory.lemmaDB.get(id)

  def addLemma(lemmaName: String, fact: Provable): Lemma = {
    require(fact.isProved, "only proved Provables would be accepted as lemmas: " + lemmaName + " got\n" + fact)
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(immutable.List("input" -> fact.toString, "output" -> "true")) :: Nil
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
    //    val generator = new ConfigurableGenerate[Formula]()
    //    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p -> inv))
    //    TactixLibrary.invGenerator = generator


    val provider = new MathematicaToolProvider(DefaultConfiguration.defaultMathematicaConfig)
    ToolProvider.setProvider(provider)

    //    val mathematica = new Mathematica()
    //    mathematica.init(DefaultConfiguration.defaultMathematicaConfig)
    //    DerivedAxioms.qeTool = mathematica
    //    TactixLibrary.tool = mathematica
  }

  def shutdownProver = {
    ToolProvider.shutdown()
    //    TactixLibrary.invGenerator = new NoneGenerate()
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

  def verify(f: Formula, tactic: BelleExpr, baseName: Option[String]): Option[Lemma] = {
    verify(Sequent(IndexedSeq.empty[Formula], IndexedSeq(f)), tactic, baseName)
  }

  def verify(s: Sequent, tactic: BelleExpr): Boolean = verify(s, tactic, None) match {
    case None => false
    case Some(_) => true
  }

  def hideAllButLastSucc(): DependentTactic = "HideAllButLastSucc" by ((seq: Sequent) => {
    cohide(seq.succ.size)
  })

  def hideSuccBut(i: Int = 1): DependentTactic = "HideSuccBut" by ((seq: Sequent) => {
    hideR(1) * (seq.succ.size - i)
  })


  def hideAnteBut(i: Int = 1): DependentTactic = "HideAnteBut" by ((seq: Sequent) => {
    hideL(-1) * (seq.ante.size - i)
  })
}


object Lemmas {

  ProofHelper.initProver

  val PRINT_LEMMA2 = false
  val PRINT_LEMMA5 = false
  val PRINT_LEMMA5L = false

  //L1 BA - DONE
  val lemma1BA: DependentPositionTactic = "Lemma1" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(b, f)) => V(pos)
  })
  val f1ba = "[?a<0;a:=b;]a>=0->[?b=-1;][?a<0;a:=b;]a>=0".asFormula
  //  val n1ba = "Proof of Lemma1 - Drop Control BA"
  //  val t1ba = implyR('R) & lemma1BA('R) & prop

  //L1 - DONE
  val lemma1: DependentPositionTactic = "Lemma1" by ((pos: Position, seq: Sequent) => {
    var t: BelleExpr = null
    var _t: BelleExpr = null
    seq.sub(pos) match {
      case Some(Box(b, f)) =>
        t = cutAt(f)(pos)
        _t = implyR('R) & V('R) & prop
    }
    t = t < (
      //use
      skip
      ,
      //show
      cohide(pos.top) & CMon(pos.inExpr) & _t
      )
    t
  })

  //L1 AB - DONE
  val lemma1AB: DependentPositionTactic = "Lemma1AB" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(a, Box(b, f))) =>
        cut(Imply(Box(a, f), Box(a, Box(b, f)))) < (
          //use
          implyL('L) < (
            hide(pos.top)
            ,
            closeId
            )
          ,
          //show
          cohide(seq.succ.size + 1) & implyR('R) & monb & V(pos) & prop
          )
    }
  })
  val f1ab = "[?a<0;a:=b;]a>=0->[?a<0;a:=b;][?b=-1;]a>=0".asFormula
  //  val n1ab = "Proof of Lemma1 - Drop Control AB"
  //  val t1ab = implyR('R) & lemma1AB('R) & prop

  //L2 - TODO!
  //TODO: REMEMBER! This only works, if the DGs that must be removed are in the right order, such that
  // the first variable only appears in the first DG, the second variable only appears in the first and second DG, and so on
  // This restriction is due to the fact that DG inverse does not handle vectors, but single variables!
  def t2_DC(elim: mutable.Seq[Variable], elimDomain: Boolean, commute: Boolean): DependentPositionTactic = "Lemma2" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(ODESystem(ode, dom), f: Formula)) => {
      //And(And(d1: Formula, d2: Formula), _)
      var t: BelleExpr = (if (PRINT_LEMMA2) print("t2_DC: start") else skip)

      val assoc = dom match {
        case And(And(_, _), _) => true
        case _ => false
      }


      if (elimDomain) {
        if (assoc)
          t = t & (if (PRINT_LEMMA2) print("t2_DC: andAssoc required!") else skip) & useAt(andAssoc, PosInExpr(0 :: Nil))(pos ++ PosInExpr(0 :: 1 :: Nil))
        t = t & (if (PRINT_LEMMA2) print("t2_DC: domainCommute...") else skip) & useAt(domainCommute)(pos)
        if (commute) {
          t = t & (if (PRINT_LEMMA2) print("t2_DC: commute is true -> commute to end") else skip)
          if (assoc)
            t = t & useAt(andAssoc, PosInExpr(0 :: Nil))(pos ++ PosInExpr(0 :: 1 :: Nil))
          t = t & useAt(domainCommute)(pos)
        }

        //Remove Evolution Domain
        t = t & (if (PRINT_LEMMA2) print("t2_DC: DCi...") else skip) & useAt("DCi", PosInExpr(1 :: Nil))(pos) //& print("domain done")

        if (commute) {
          t = t & (if (PRINT_LEMMA2) print("t2_DC: commute is true -> commute back") else skip)
          //          if (assoc)
          //            t = t & useAt(andAssoc, PosInExpr(0 :: Nil))(pos ++ PosInExpr(0 :: 1 :: Nil))
          t = t & useAt(domainCommute)(pos)
        }
      }


      //Remove Differential Equations
      t = t & useAt(", commute", PosInExpr(1 :: Nil))(pos) & (if (PRINT_LEMMA2) print("commuted") else skip)
      t = t & Lemma2Stuff.rotateOrEliminateAll(elim)(pos)
      t
    }
  })

  def lemma2_DC(elim: mutable.Seq[Variable], elimDomain: Formula): DependentPositionTactic = "Lemma2" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(p, Box(ODESystem(ode: DifferentialProgram, And(dom, dt: Formula)), f: Formula))) => {
      if (PRINT_LEMMA2) {
        println("lemma2_DC: elim='" + elim + "', elimDomain='" + elimDomain + "'")
      }

      val trueElimDomain = if (elimDomain == null) True else elimDomain

      var commute = false
      val d = dom match {
        case f if (f.equals(True)) =>
          if (PRINT_LEMMA2) {
            println("lemma2_DC: using whole dom because dom (" + f + ") is True")
          }
          dom
        case And(d1: Formula, d2: Formula) if (d1.equals(trueElimDomain)) =>
          if (PRINT_LEMMA2) {
            println("lemma2_DC: using domain 2 in cut because elimdomain (" + trueElimDomain + ") is d1")
          }
          d2
        case And(d1: Formula, d2: Formula) if (d2.equals(trueElimDomain)) =>
          if (PRINT_LEMMA2) {
            println("lemma2_DC: using domain 1 in cut because elimdomain (" + trueElimDomain + ") is d2")
          }
          commute = true
          d1
        //        case f if (f.equals(elimDomain)) =>
        //          if (PRINT_LEMMA2) {
        //            println("lemma2_DC: using True in cut because elimdomain (" + elimDomain + ") is the whole evolution domain --> MUST be True --> dom=" + dom)
        //          }
        //          True
        //        case f: Formula =>
        //          if (PRINT_LEMMA2) {
        //            println("lemma2_DC: using whole evolution domain in cut because elimdomain (" + elimDomain + ") is not in formula")
        //          }
        //          f
      }


      (if (PRINT_LEMMA2) print("lemma2_DC: cutting: " + Imply(Box(p, Box(ODESystem(Lemma2Stuff.removeODEs(ode, elim), And(d, dt)), f: Formula)), Box(p, Box(ODESystem(ode, And(dom, dt)), f)))) else skip) &
        cut(Imply(Box(p, Box(ODESystem(Lemma2Stuff.removeODEs(ode, elim), And(d, dt)), f: Formula)), Box(p, Box(ODESystem(ode, And(dom, dt)), f)))) < (
          //use
          (if (PRINT_LEMMA2) print("lemma2_DC: use cut") else skip) & implyL(-seq.ante.size - 1) < (
            hide(pos.top)
            ,
            closeId
            ) & (if (PRINT_LEMMA2) print("lemma2_DC: done use cut") else skip)
          ,
          //show
          (if (PRINT_LEMMA2) print("lemma2_DC: show cut") else skip) & cohide(seq.succ.size + 1) & implyR('R) & monb &
            (if (PRINT_LEMMA2) print("lemma2_DC: applying t2_DC...") else skip) & t2_DC(elim, !dom.equals(True), commute)('R) &
            prop & (if (PRINT_LEMMA2) print("lemma2_DC: show cut done - PROP") else skip)
          ) & (if (PRINT_LEMMA2) print("lemma2_DC: lemma 2 done!") else skip)
    }
  })

  private object Lemma2Stuff {
    def removeODEs(ode: DifferentialProgram, elim: mutable.Seq[Variable]): DifferentialProgram = {
      val odes = collectODEs(ode, elim)
      var ret: DifferentialProgram = odes(0)
      (1 until odes.size) foreach { i => ret = DifferentialProduct(ret, odes(i)) }
      ret
    }

    private def collectODEs(ode: DifferentialProgram, elim: mutable.Seq[Variable]): Seq[AtomicODE] = {
      ode match {
        case a: AtomicODE => if (elim.contains(a.xp.x)) Seq.empty[AtomicODE] else a :: Nil
        case d: DifferentialProduct => collectODEs(d.left, elim) ++ collectODEs(d.right, elim)
      }

    }

    def rotateOrEliminate(elim: mutable.Seq[Variable]): DependentPositionTactic = "Rotate DG and eliminate Variables until Time is reached" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(ODESystem(ode, constraint), f: Formula)) => {
        var t: BelleExpr = skip
        val v = nextVariable(ode)
        if (elim.contains(v)) {
          t = t & (if (PRINT_LEMMA2) print("elim " + v) else skip) &
            cut(Forall(Seq(v), sequent.succ(pos.top.getPos - 1))) < (
              allL(v, v)(-sequent.ante.length - 1) & prop, hide(pos.top)
              ) & (if (PRINT_LEMMA2) print("Lemma2: using at DGi") else skip) & useAt("DG inverse differential ghost implicational", PosInExpr(1 :: Nil))(pos)
        }
        else {
          t = t & (if (PRINT_LEMMA2) print("rotate " + v) else skip) &
            useAt(", commute", PosInExpr(1 :: Nil))(pos)
        }
        t
      }
    })

    def rotateOrEliminateAll(elim: mutable.Seq[Variable]): DependentPositionTactic = "Rotate DG and eliminate Variables until Time is reached" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(ODESystem(ode, constraint), f: Formula)) => {
        var t: BelleExpr = (if (PRINT_LEMMA2) print("Lemma2: rotateOrEliminate - elim: " + elim) else skip) & rotateOrEliminate(elim)(pos) & (if (PRINT_LEMMA2) print("after remove/skip 1") else skip)
        (1 to countDiff(ode) - 2) foreach (i => t = t & rotateOrEliminate(elim)(pos) & (if (PRINT_LEMMA2) print("after remove/skip " + (i + 1)) else skip))
        t & (if (PRINT_LEMMA2) print("done rotateOrEliminateAll") else skip)
      }
    })

    def countDiff(dp: DifferentialProgram): Integer = dp match {
      case a: AtomicODE => 1
      case DifferentialProduct(dp1, dp2) => countDiff(dp1) + countDiff(dp2)
    }

    private def nextVariable(dp: DifferentialProgram): Variable = dp match {
      case AtomicODE(s, _) => //println("a: " + s.x);
        s.x
      case DifferentialProduct(a: AtomicODE, _) => //println("d: " + a.xp.x);
        a.xp.x
    }
  }

  val f2 = ("[{t'=1,x1'=c1(x1,x2,x3,T),x2'=c2(x1,x2,x3,T),x3'=c3(x1,x2,x3,T)&H1(x1,x2,x3,T)&T>0}]A(x1,x2,x3,T)" +
    "->[{t'=1,x1'=c1(x1,x2,x3,T),x2'=c2(x1,x2,x3,T),x3'=c3(x1,x2,x3,T),y1'=d1(y1,y2,y3,y4,T),y2'=d2(y2,y3,y4,T),y3'=d3(y3,y4,T),y4'=d4(y4,T)& (H1(x1,x2,x3,T)&G1(y1,y2,y3,y4,T))&T>0}]A(x1,x2,x3,T)").asFormula
  val n2 = "Proof of Lemma2 - Drop Plant"
  //  val t2 = implyR('R) & lemma2(1, 3, 4, false) & prop
  //NOT possible because we cannot proof this as lemma
  //  lazy val lemma2: Lemma = lemma(f2, n2, t2)
  //  lazy val lemma2T = TactixLibrary.byUS(lemma2)

  //L3 - DONE
  lazy val f3 = "([x:=*;]A(x))->([x:=p(x);]A(x))".asFormula
  lazy val n3 = "Proof of Lemma3 - Overapproximate Assignment"
  lazy val t3 = implyR('R) & assignb('R) & randomb('L) & allL("x".asVariable, "p(x)".asTerm)('L) & close(-1, 1)
  lazy val lemma3: Lemma = lemma(f3, n3, t3)
  lazy val lemma3T = TactixLibrary.byUS(lemma3)

  //Alternative: ls(implyR) & useAt(assignbEquationalAxiom)(1) & useAt(allSubstitute)(1) & la(randomb) & la(allL("x".asVariable, "p".asTerm)) & close(-1, 1)


  //L4 - DONE
  val f4_1 = "[x_:=a_; y_:=b_;]A_(x_,y_) <-> [y_:=b_; x_:=a_;]A_(x_,y_)".asFormula
  //  val n4_1 = "Proof of Lemma4 - Reorder Programs 1"
  val t4_1 = implyR('R) &
    (
      // ->
      (composeb('R) & composeb('L) & assignb('R) * 2 & assignb('L) * 2 & prop) |
        // <-
        (composeb('R) & composeb('L) & assignb('R) & assignb('R) & assignb('L) & assignb('L) & prop)
      )
  /**
    * [x_:=a_; y_:=b_;]A_(x_,y_) <-> [y_:=b_; x_:=a_;]A_(x_,y_)
    */
  lazy val lemma4_1T: DependentPositionTactic = "Apply Lemma4_1" by ((pos: Position, seq: Sequent) => {
    var t: BelleExpr = null
    var _t: BelleExpr = null
    seq.sub(pos) match {
      case Some(Box(Compose(Assign(x, a), Assign(y, b)), f)) =>
        t = cutAt(Box(Compose(Assign(y, b), Assign(x, a)), f))(pos)
        _t = t4_1
      case Some(Box(Assign(x, a), Box(Assign(y, b), f))) =>
        t = cutAt(Box(Assign(y, b), Box(Assign(x, a), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_1
    }
    t = t < (
      //use
      skip
      ,
      //show
      cohide(pos.top) & CMon(pos.inExpr) & _t
      )
    t
  })
  //TODO: That would be what we want, but "fst" and "snd" do not work yet!
  //  lazy val lemma4_1: Lemma = lemma(f4_1, n4_1, t4_1)
  //  lazy val lemma4_1T: DependentPositionTactic = "Apply Lemma4_1" by ((pos: Position, seq: Sequent) => {
  //    seq.sub(pos) match {
  //      case Some(Box(Compose(Assign(x, a), Assign(y, b)), f)) =>
  //        val subst = RenUSubst(("x_".asVariable, x) :: ("a_".asVariable, a) :: ("y_".asVariable, y) :: ("x_".asVariable, y) :: ("A_(.(Real,Real))".asFormula, f.replaceFree(x, "fst(.(.,.))".asTerm).replaceFree(y, "snd(.(.,.))".asTerm)) :: Nil)
  //        useAt(lemma4_1, PosInExpr(0 :: Nil), (s: Subst) => subst)(pos)
  //        print("")
  //    }
  //  })

  val f4_2 = "[x_:=*; y_:=*;]A_(x_,y_) <-> [y_:=*; x_:=*;]A_(x_,y_)".asFormula

  //  val n4_2 = "Proof of Lemma4 - Reorder Programs 2"
  def t4_2(x: Variable = "x_".asVariable, y: Variable = "y_".asVariable): BelleExpr = implyR('R) & composeb('R) & composeb('L) & (randomb('R) & allR('R)) * 2 & randomb('L) & allL(y)('L) & randomb('L) & allL(x)('L) & prop

  //  lazy val lemma4_2: Lemma = lemma(f4_2, n4_2, t4_2)

  /**
    * [x_:=*; y_:=*;]A_(x_,y_) <-> [y_:=*; x_:=*;]A_(x_,y_)
    */
  lazy val lemma4_2T: DependentPositionTactic = "Apply Lemma4_2" by ((pos: Position, seq: Sequent) => {
    var t: BelleExpr = null
    var _t: BelleExpr = null
    seq.sub(pos) match {
      case Some(Box(Compose(AssignAny(x), AssignAny(y)), f)) =>
        t = cutAt(Box(Compose(AssignAny(y), AssignAny(x)), f))(pos)
        _t = t4_2(x, y)
      case Some(Box(AssignAny(x), Box(AssignAny(y), f))) =>
        t = cutAt(Box(AssignAny(y), Box(AssignAny(x), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_2(x, y)
    }

    t = t < (
      //use
      skip
      ,
      //show
      cohide(pos.top) & CMon(pos.inExpr) & _t
      )
    t
  })
  val f4_3 = "[x_:=*; y_:=b_;]A_(x_,y_) <-> [y_:=b_; x_:=*;]A_(x_,y_)".asFormula
  val n4_3 = "Proof of Lemma4 - Reorder Programs 3"

  def t4_3_1(x: Variable = "x_".asVariable) = implyR(1) & composeb('R) & composeb('L) & assignb('R) & randomb('R) & allR('R) & randomb('L) & allL(x)('L) & assignb('L) & prop

  def t4_3_2(x: Variable = "x_".asVariable) = implyR(1) & composeb('R) & composeb('L) & randomb('R) & allR('R) & assignb('R) & assignb('L) & randomb('L) & allL(x)('L) & prop

  /**
    * [x_:=*; y_:=b_;]A_(x_,y_) <-> [y_:=b_; x_:=*;]A_(x_,y_)
    */
  lazy val lemma4_3T: DependentPositionTactic = "Apply Lemma4_3" by ((pos: Position, seq: Sequent) => {
    var t: BelleExpr = null
    var _t: BelleExpr = null
    seq.sub(pos) match {
      case Some(Box(Compose(AssignAny(x), Assign(y, b)), f)) =>
        t = cutAt(Box(Compose(Assign(y, b), AssignAny(x)), f))(pos)
        _t = t4_3_2(x)
      case Some(Box(Compose(Assign(y, b), AssignAny(x)), f)) =>
        t = cutAt(Box(Compose(AssignAny(x), Assign(y, b)), f))(pos)
        _t = t4_3_1(x)
      case Some(Box(AssignAny(x), Box(Assign(y, b), f))) =>
        t = cutAt(Box(Assign(y, b), Box(AssignAny(x), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_3_2(x)
      case Some(Box(Assign(y, b), Box(AssignAny(x), f))) =>
        t = cutAt(Box(AssignAny(x), Box(Assign(y, b), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_3_1(x)
    }
    t = t < (
      //use
      skip
      ,
      //show
      cohide(pos.top) & CMon(pos.inExpr) & _t
      )
    t
  })
  //  lazy val lemma4_3: Lemma = lemma(f4_3, n4_3, t4_3())

  val f4_4 = "[x_:=*; ?B_(a_);]A_(x_,a_) <-> [?B_(a_); x_:=*;]A(x_,a_)".asFormula

  //  val n4_4 = "Proof of Lemma4 - Reorder Programs 4"
  def t4_4_1(x: Variable = "x_".asVariable) = implyR(1) & composeb('R) & composeb('L) & testb('R) & randomb(1, 1 :: Nil) & testb(-1, 1 :: Nil) & randomb('L) & implyR('R) & allR('R) & allL(x)('L) & implyL('L) & prop

  def t4_4_2(x: Variable = "x_".asVariable) = implyR(1) & composeb('R) & composeb('L) & randomb('R) & allR('R) & randomb(-1, 1 :: Nil) & allL(x)(-1, 1 :: Nil) & close(-1, 1)

  //  lazy val lemma4_4: Lemma = lemma(f4_4, n4_4, t4_4)
  /**
    * [x_:=*; ?B_(a_);]A_(x_,a_) <-> [?B_(a_); x_:=*;]A(x_,a_)
    */
  lazy val lemma4_4T: DependentPositionTactic = "Apply Lemma4_4" by ((pos: Position, seq: Sequent) => {
    var t: BelleExpr = null
    var _t: BelleExpr = null
    seq.sub(pos) match {
      case Some(Box(Compose(AssignAny(x), Test(b)), f)) =>
        t = cutAt(Box(Compose(Test(b), AssignAny(x)), f))(pos)
        _t = t4_4_2(x)
      case Some(Box(Compose(Test(b), AssignAny(x)), f)) =>
        t = cutAt(Box(Compose(AssignAny(x), Test(b)), f))(pos)
        _t = t4_4_1(x)
      case Some(Box(AssignAny(x), Box(Test(b), f))) =>
        t = cutAt(Box(Test(b), Box(AssignAny(x), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_4_2(x)
      case Some(Box(Test(b), Box(AssignAny(x), f))) =>
        t = cutAt(Box(AssignAny(x), Box(Test(b), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_4_1(x)
    }
    t = t < (
      //use
      skip
      ,
      //show
      cohide(pos.top) & CMon(pos.inExpr) & _t
      )
    t
  })

  val f4_5 = "[x_:=a_; ?B_(a_);]A_(x_,a_) <-> [?B_(a_); x_:=a_;]A_(x_,a_)".asFormula
  //  val n4_5 = "Proof of Lemma4 - Reorder Programs 5"
  val t4_5_1 = implyR(1) & composeb('R) & composeb('L) & assignb('L) & assignb(1, 1 :: Nil) & prop
  val t4_5_2 = implyR(1) & composeb('R) & composeb('L) & assignb('R) & assignb(-1, 1 :: Nil) & prop
  //  lazy val lemma4_5: Lemma = lemma(f4_5, n4_5, t4_5)

  /**
    * [x_:=a_; ?B_(a_);]A_(x_,a_) <-> [?B_(a_); x_:=a_;]A_(x_,a_)
    */
  lazy val lemma4_5T: DependentPositionTactic = "Apply Lemma4_5" by ((pos: Position, seq: Sequent) => {
    var t: BelleExpr = null
    var _t: BelleExpr = null
    seq.sub(pos) match {
      case Some(Box(Compose(Assign(x, a), Test(b)), f)) =>
        t = cutAt(Box(Compose(Test(b), Assign(x, a)), f))(pos)
        _t = t4_5_2
      case Some(Box(Compose(Test(b), Assign(x, a)), f)) =>
        t = cutAt(Box(Compose(Assign(x, a), Test(b)), f))(pos)
        _t = t4_5_1
      case Some(Box(Test(b), Box(Assign(x, a), f))) =>
        t = cutAt(Box(Assign(x, a), Box(Test(b), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_5_1
      case Some(Box(Assign(x, a), Box(Test(b), f))) =>
        t = cutAt(Box(Test(b), Box(Assign(x, a), f)))(pos)
        _t = useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_5_2
    }
    t = t < (
      //use
      skip
      ,
      //show
      cohide(pos.top) & CMon(pos.inExpr) & _t
      )
    t
  })

  val f4_6 = "[?F_(??); ?G_(??);]A_(??) <-> [?G_(??); ?F_(??);]A_(??)".asFormula
  //  val n4_6 = "Proof of Lemma4 - Reorder Programs 6"
  val t4_6 = implyR('R) & composeb('R) & composeb('L) & testb('R) & testb(1, 1 :: Nil) & testb('L) & testb(-1, 1 :: Nil) & prop
  //  lazy val lemma4_6: Lemma = lemma(f4_6, n4_6, t4_6)

  /**
    * [?F_(??); ?G_(??);]A_(??) <-> [?G_(??); ?F_(??);]A_(??)
    */
  lazy val lemma4_6T: DependentPositionTactic = "Apply Lemma4_6" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(Compose(Test(a), Test(b)), f)) =>
        cutAt(Box(Compose(Test(b), Test(a)), f))(pos) < (
          //use
          skip
          ,
          //show
          cohide(pos.top) & CMon(pos.inExpr) & t4_6
          )
      case Some(Box(Test(a), Box(Test(b), f))) =>
        cutAt(Box(Test(b), Box(Test(a), f)))(pos) < (
          //use
          skip
          ,
          //show
          cohide(pos.top) & CMon(pos.inExpr) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) & t4_6
          )
    }
  })

  //Lemma 5 - DONE   {|^@|}
  val f5 = "[a{|^@|};]F_(||) -> ( [a{|^@|};?F_(||);]A_(||) <-> [a{|^@|};]A_(||) )".asFormula
  val n5 = "Proof of Lemma5 - Introduce Test"
  val t5 = implyR('R) & equivR('R) < (
    // ->
    (if (PRINT_LEMMA5) print("-> -1") else skip) & implyRi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(1).asInstanceOf[SuccPos]) & composeb(1, 0 :: Nil) & testb(1, 0 :: 1 :: Nil) &
      (if (PRINT_LEMMA5) print("-> 1") else skip) & useAt("K modal modus ponens", PosInExpr(1 :: Nil))('R) & monb &
      (if (PRINT_LEMMA5) print("-> 2") else skip) & implyR('R) & modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & closeId &
      (if (PRINT_LEMMA5) print("-> 3") else skip)
    ,
    // <-
    (if (PRINT_LEMMA5) print("<- 0") else skip) & implyRi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(1).asInstanceOf[SuccPos]) &
      (if (PRINT_LEMMA5) print("<- 1") else skip) & composeb(1, 1 :: Nil) & testb(1, 1 :: 1 :: Nil) &
      (if (PRINT_LEMMA5) print("<- 2") else skip) & K('R) &
      (if (PRINT_LEMMA5) print("<- 3") else skip) & monb & implyR('R) & implyR('R) & closeId
    )

  //  /**
  //    * Applies Lemma 5 to introduce a test.
  //    * This results in two proof goals: (1) [a_;]F_(||) must be verified, (2) introduces the test.
  //    *
  //    * @param test The test to be introduced.
  //    * @return The tactic applying Lemma 5
  //    */
  //  def lemma5T(test: Formula): DependentPositionTactic = "Apply Lemma5" by ((pos: Position, seq: Sequent) => {
  //    seq.sub(pos) match {
  //      case Some(Box(p: Program, f: Formula)) =>
  //        cut(Imply(Box(p, test), Equiv(Box(Compose(p, Test(test)), f), Box(p, f)))) < (
  //          //use
  //          implyL(Position(-seq.ante.size - 1)) < (
  //            hideR(1) * seq.succ.size
  //            ,
  //            equivRewriting(Position(-seq.ante.size - 1), pos) & hideL(Position(-seq.ante.size - 1))
  //            )
  //
  //          ,
  //          //show
  //          cohide(seq.succ.size + 1) & t5
  //          )
  //    }
  //  })

  lazy val lemma5: Lemma = lemma(f5, n5, t5)

  /**
    * Applies Lemma 5 to introduce a test.
    * [a_;]F_(||) -> ( [a_;?F_(||);]A_(||) <-> [a_;]A_(||) )
    * This results in two proof goals: (1) use the introduced test, (2) [a_;]F_(||) must be verified.
    *
    * @param test The test to be introduced.
    * @return The tactic applying Lemma 5
    */
  def lemma5T(test: Formula): DependentPositionTactic = "Apply Lemma5" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(p: Program, f: Formula)) =>
        useAt("ANON", lemma5.fact, PosInExpr(1 :: 1 :: Nil), uso => uso match {
          case Some(s) => s ++ RenUSubst(("F_(||)".asFormula, test) :: Nil)
        })(pos)
    }
  })


  //Lemma 5 left - TODO
  val f5L = "F_(||) -> ( [?F_(||);]A_(||) <-> A_(||) )".asFormula
  val n5L = "Proof of Lemma5 - Introduce Test Left"
  val t5L = implyR('R) & equivR('R) < (
    // -> implyRi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(1).asInstanceOf[SuccPos]) &
    (if (PRINT_LEMMA5L) print("->") else skip) & testb('L) & implyL('L) < (closeId, closeId)
    ,
    // <-
    (if (PRINT_LEMMA5L) print("<-") else skip) & testb('R) & implyR('R) & closeId
    )
  lazy val lemma5L: Lemma = lemma(f5L, n5L, t5L)

  /**
    * Applies Lemma 5 to introduce a test.
    * [a_;]F_(||) -> ( [a_;?F_(||);]A_(||) <-> [a_;]A_(||) )
    * This results in two proof goals: (1) use the introduced test, (2) [a_;]F_(||) must be verified.
    *
    * @param test The test to be introduced.
    * @return The tactic applying Lemma 5
    */
  def lemma5LT(test: Formula): DependentPositionTactic = "Apply Lemma5" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(f: Formula) =>
        useAt("ANON", lemma5L.fact, PosInExpr(1 :: 1 :: Nil), uso => uso match {
          case Some(s) => s ++ RenUSubst(("F_(||)".asFormula, test) :: Nil)
        })(pos)
    }
  })

  //Lemma 6 - DONE
  //  val f6 = "(([?G(??);]A(??)) & (F(??)->G(??))) -> [?F(??);]A(??)".asFormula
  val f6 = "(F(||)->G(||)) -> (([?G(||);]A(||)) -> [?F(||);]A(||))".asFormula
  val n6 = "Proof of Lemma6 - Weaken Test"
  val t6 = implyR('R) & implyR('R) & testb('R) & testb('L) & prop
  val l6 = lemma(f6, n6, t6)

  /**
    * Applies Lemma 6 to weaken a test.
    * (F(||)->G(||)) -> (([?G(||);]A(||)) -> [?F(||);]A(||))
    * This results in two proof goals: (1) F(||)->G(||) must be verified, (2) use the weakened test.
    *
    * @param g The target test
    * @return The tactic applying Lemma 6
    */
  def lemma6T(g: Formula): DependentPositionTactic = "Apply Lemma6" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(f: Test, a: Formula)) =>
        val (ctx, _) = seq.at(pos)

        cutAt(Box(Test(g), a))(pos) < (
          //use
          skip
          ,
          //show
          //          ProofHelper.hideAllButLastSucc() &
          cut(ctx.apply(Imply(f.cond, g))) < (
            ProofHelper.hideSuccBut() & ProofHelper.hideAnteBut() &
              implyR('R) & andLi &
              ((useAt(DerivedAxioms.boxAnd, PosInExpr(1 :: Nil))(-1) & implyRi & CMon(PosInExpr(1 :: Nil)) & implyR('R)) *) &
              andL('L) & testb('L) & testb('R) &
              implyR('R) & implyL(-1) < (closeId, modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & closeId),
            ProofHelper.hideSuccBut() & skip
            )
          )
      //        < (
      //          //use
      //          implyL(Position(-seq.ante.size - 1)) < (
      //            hide(1) * seq.succ.size
      //            ,
      //            implyL(Position(-seq.ante.size - 1)) < (
      //              hide(pos.top.getPos),
      //              prop
      //              )
      //            )
      //          ,
      //          //show
      //          cohide(seq.succ.size + 1) & t6
      //          )
    }
  })


  //  def lemma6T(g: Formula): DependentPositionTactic = "Apply Lemma6" by ((pos: Position, seq: Sequent) => {
  //    seq.sub(pos) match {
  //      case Some(Box(f: Test, a: Formula)) =>
  //        cut(Imply(Imply(f.cond, g), Imply(Box(Test(g), a), Box(f, a)))) < (
  //          //use
  //          implyL(Position(-seq.ante.size - 1)) < (
  //            hide(1) * seq.succ.size
  //            ,
  //            implyL(Position(-seq.ante.size - 1)) < (
  //              hide(pos.top.getPos),
  //              prop
  //              )
  //            )
  //          ,
  //          //show
  //          cohide(seq.succ.size + 1) & t6
  //          )
  //    }
  //  })


  //Corollary 1 - DONE
  val f7 = "[a;](F(||)->G(||)) -> (([a;][?G(||);]A(||)) -> [a;][?F(||);]A(||))".asFormula
  val n7 = "Proof of Corollary1- Weaken Test Context"
  val t7 = implyR('R) & implyR('R) & andLi & useAt(DerivedAxioms.boxAnd, PosInExpr(1 :: Nil))('L) & monb & andL('L) &
    implyRi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(1).asInstanceOf[SuccPos]) &
    implyRi(SeqPos(-1).asInstanceOf[AntePos], SeqPos(1).asInstanceOf[SuccPos]) & t6

  /**
    * Applies Lemma 7 (i.e., Corollary 1) to weaken a test.
    * [a;](F(||)->G(||)) -> (([a;][?G(||);]A(||)) -> [a;][?F(||);]A(||))
    * This results in two proof goals: (1) [a;](F(||)->G(||)) must be verified, (2) use the weakened test.
    *
    * @param g The target test
    * @return The tactic applying Lemma 7 (i.e., Corollary 1)
    */
  def lemma7T(g: Formula): DependentPositionTactic = "Apply Lemma7" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(p, Box(f: Test, a: Formula))) =>
        cut(Imply(Box(p, Imply(f.cond, g)), Imply(Box(p, Box(Test(g), a)), Box(p, Box(f, a))))) < (
          //use
          implyL(Position(-seq.ante.size - 1)) < (
            hide(1) * seq.succ.size
            ,
            implyL(Position(-seq.ante.size - 1)) < (
              hide(pos),
              prop
              )
            )
          ,
          //show
          cohide(seq.succ.size + 1) & t7
          )
    }
  })

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
        val evidence = ToolEvidence(immutable.List("input" -> proof.toString, "output" -> "true")) :: Nil
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
    ProofHelper.initProver
    //        proofAll
    //
    //    println("==> Test Lemma 1BA - proved? " + TactixLibrary.proveBy("[a:=2;b:=4;?a>0;]a>0".asFormula,
    //      composeb('R) & composeb(1, 1 :: Nil) & lemma1BA(1, 1 :: Nil) & assignb('R) & testb('R) & prop).isProved)
    //    println("==> Test Lemma 1AB - proved? " + TactixLibrary.proveBy("[a:=2;?a>0;]a>0 -> [a:=2;b:=4;?a>0;]a>0".asFormula,
    //      implyR('R) & composeb('R) & composeb(1, 1 :: Nil) & lemma1(1, 1 :: Nil) & normalize).isProved)
    //    println("==> Test Lemma 2 - proved? " + TactixLibrary.proveBy("t=0&a=0 -> [a:=2;{t'=1,a'=1,b'=1&(a<10&b<10)&t<10}]a<20".asFormula,
    //      implyR('R) & composeb('R) &
    //        lemma2_DC(mutable.Seq("b".asVariable), "b<10".asFormula)('R) & assignb('R) & diffSolve('R) & QE & print("y")
    //    ).isProved)
    //    println("==> Test Lemma 3 - proved? " + TactixLibrary.proveBy("[a:=4;?a>0;]a>0".asFormula,
    //      composeb('R) & useAt("ANON", lemma3.fact, PosInExpr(1 :: Nil))('R) & randomb('R) & allR('R) & testb('R) & prop).isProved)
    //    println("==> Test Lemma 4_1 - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=a1;b:=b1;]a>0 -> [?c>0;c:=32;][x:=y;][b:=b1;a:=a1;](a>0)".asFormula,
    //      implyR('R) & lemma4_1T(1, 1 :: 1 :: Nil) & print("hihi 41") & closeId).isProved)
    //    println("==> Test Lemma 4_1 split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=a1;][b:=b1;]a>0 -> [?c>0;c:=32;][x:=y;][b:=b1;][a:=a1;](a>0)".asFormula,
    //      implyR('R) & lemma4_1T(1, 1 :: 1 :: Nil) & print("hihi 41s") & closeId).isProved)
    //    println("==> Test Lemma 4_2 - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=*;b:=*;]a>0 -> [?c>0;c:=32;][x:=y;][b:=*;a:=*;]a>0".asFormula,
    //      implyR('R) & lemma4_2T(1, 1 :: 1 :: Nil) & print("hihi 42") & closeId).isProved)
    //    println("==> Test Lemma 4_2 split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=*;][b:=*;]a>0 -> [?c>0;c:=32;][x:=y;][b:=*;][a:=*;]a>0".asFormula,
    //      implyR('R) & lemma4_2T(1, 1 :: 1 :: Nil) & print("hihi 42s") & closeId).isProved)
    //    println("==> Test Lemma 4_3 '->' - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=*;b:=b1;]a>0 -> [?c>0;c:=32;][x:=y;][b:=b1;a:=*;](a>0)".asFormula,
    //      implyR('R) & lemma4_3T(1, 1 :: 1 :: Nil) & print("hihi 43->") & closeId).isProved)
    //    println("==> Test Lemma 4_3 '<-' - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=a1;b:=*;]a>0 -> [?c>0;c:=32;][x:=y;][b:=*;a:=a1;](a>0)".asFormula,
    //      implyR('R) & lemma4_3T(1, 1 :: 1 :: Nil) & print("hihi 43<-") & closeId).isProved)
    //    println("==> Test Lemma 4_3 '->' split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=*;][b:=b1;]a>0 -> [?c>0;c:=32;][x:=y;][b:=b1;][a:=*;](a>0)".asFormula,
    //      implyR('R) & lemma4_3T(1, 1 :: 1 :: Nil) & print("hihi 43->s") & closeId).isProved)
    //    println("==> Test Lemma 4_3 '<-' split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=a1;][b:=*;]a>0 -> [?c>0;c:=32;][x:=y;][b:=*;][a:=a1;](a>0)".asFormula,
    //      implyR('R) & lemma4_3T(1, 1 :: 1 :: Nil) & print("hihi 43<-s") & closeId).isProved)
    //    println("==> Test Lemma 4_4 '->' - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=*;?(b>0);]a>0 -> [?c>0;c:=32;][x:=y;][?(b>0);a:=*;](a>0)".asFormula,
    //      implyR('R) & lemma4_4T(1, 1 :: 1 :: Nil) & print("hihi 44->") & closeId).isProved)
    //    println("==> Test Lemma 4_4 - '<-' proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][?(b>0);a:=*;]a>0 -> [?c>0;c:=32;][x:=y;][a:=*;?(b>0);](a>0)".asFormula,
    //      implyR('R) & lemma4_4T(1, 1 :: 1 :: Nil) & print("hihi 44<-") & closeId).isProved)
    //    println("==> Test Lemma 4_4 '->' split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=*;][?(b>0);]a>0 -> [?c>0;c:=32;][x:=y;][?(b>0);][a:=*;](a>0)".asFormula,
    //      implyR('R) & lemma4_4T(1, 1 :: 1 :: Nil) & print("hihi 44->s") & closeId).isProved)
    //    println("==> Test Lemma 4_4 '<-' split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][?(b>0);][a:=*;]a>0 -> [?c>0;c:=32;][x:=y;][a:=*;][?(b>0);](a>0)".asFormula,
    //      implyR('R) & lemma4_4T(1, 1 :: 1 :: Nil) & print("hihi 44<-s") & closeId).isProved)
    //    println("==> Test Lemma 4_5 '->' - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=a1;?(b>0);]a>0 -> [?c>0;c:=32;][x:=y;][?(b>0);a:=a1;](a>0)".asFormula,
    //      implyR('R) & lemma4_5T(1, 1 :: 1 :: Nil) & print("hihi45->") & closeId).isProved)
    //    println("==> Test Lemma 4_5 '<-' - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][?(b>0);a:=a1;]a>0 -> [?c>0;c:=32;][x:=y;][a:=a1;?(b>0);](a>0)".asFormula,
    //      implyR('R) & lemma4_5T(1, 1 :: 1 :: Nil) & print("hihi 45<-") & closeId).isProved)
    //    println("==> Test Lemma 4_5 '->' split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][a:=a1;][?(b>0);]a>0 -> [?c>0;c:=32;][x:=y;][?(b>0);][a:=a1;](a>0)".asFormula,
    //      implyR('R) & lemma4_5T(1, 1 :: 1 :: Nil) & print("hihi 45->s") & closeId).isProved)
    //    println("==> Test Lemma 4_5 '<-' split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][?(b>0);][a:=a1;]a>0 -> [?c>0;c:=32;][x:=y;][a:=a1;][?(b>0);](a>0)".asFormula,
    //      implyR('R) & lemma4_5T(1, 1 :: 1 :: Nil) & print("hihi 45<-s") & closeId).isProved)
    //    println("==> Test Lemma 4_6 - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][?(a>0);?(b>0);]a>0 -> [?c>0;c:=32;][x:=y;][?(b>0);?(a>0);](a>0)".asFormula,
    //      implyR('R) & lemma4_6T(1, 1 :: 1 :: Nil) & print("hihi 46") & closeId).isProved)
    //    println("==> Test Lemma 4_6 split - proved? " + TactixLibrary.proveBy("[?c>0;c:=32;][x:=y;][?(a>0);][?(b>0);]a>0 -> [?c>0;c:=32;][x:=y;][?(b>0);][?(a>0);](a>0)".asFormula,
    //      implyR('R) & lemma4_6T(1, 1 :: 1 :: Nil) & print("hihi 46 split") & closeId).isProved)
//    println("==> Test Lemma 5 - proved? " + TactixLibrary.proveBy("a>5 -> [b:=0;]a>0".asFormula,
//      implyR('R) & lemma5T("a>5".asFormula)('R) < (
//        //use test
//        composeb('R) & assignb('R) & testb('R) & implyR('R) & QE,
//        //show
//        V('R) & prop
//        )).isProved)
//    println("==> Test Lemma 5 Left - proved? " + TactixLibrary.proveBy("a>5 -> [b:=0;]a>0".asFormula,
//      implyR('R) & lemma5LT("a>5".asFormula)('R) < (
//        //use test
//        testb('R) & implyR('R) & assignb('R) & QE,
//        //show
//        prop
//        )).isProved)


    println("==> Test Lemma 6 - proved? " + TactixLibrary.proveBy("([x:=2;][a:=10;](a>5->(a>0&c>0))) -> [x:=2;][a:=10;][?a>5;]a>0".asFormula,
      implyR('R) & print("before lemma6") & lemma6T("a>0".asFormula)(1, 1 :: 1 :: Nil) &
        print("after lemma6") < (
          print("use") & monb & monb & testb('R) & prop & print("use done?"),
          print("show") & hideL(-1) & assignb('R) & assignb('R) & QE & print("show done?")
          )).isProved)
    println("==> Test Lemma 7 - proved? " + TactixLibrary.proveBy("([a:=42;](a>5->(a>0&c>0))) -> [a:=42;][?a>5;]a>0".asFormula,
      implyR('R) & lemma7T("a>0".asFormula)('R) < (
        monb & QE,
        monb & testb('R) & prop
        )).isProved)


    // Lemma 5 using the OLD version of the tactic, without the Lemma
    //    println("Test Lemma 5 - proved? " + TactixLibrary.proveBy("a>5 -> [b:=0;]a>0".asFormula, implyR('R) & lemma5T("a>5".asFormula)('R) < (
    //      V('R) & closeId,
    //      composeb('R) & V('R) & testb('R) & QE
    //      )).isProved)

    //    val f = f4_1
    //    val n = n4_1
    //    val t = t4_1
    //    if (null == lemma(f, n, t))
    //      println(" Error proving '" + n + "'!")
    //    else
    //      println("Verified " + n)
    ProofHelper.shutdownProver
  }
}
