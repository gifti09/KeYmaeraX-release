/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import TacticFactory._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ElidingProvable$}

import scala.collection.immutable._

/**
  * An Axiomatic ODE solver.
  * Current limitations:
  * - No support for explicit-form diamond ODEs/box ODEs in context: <{x'=0*x+1}>P, ![{x'=0*x+1}]P
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
object AxiomaticODESolver {
  private val ODE_DEBUGGER = false

  private val namespace = "odesolver"

  private lazy val simplifier = SimplifierV3.simpTac()

  /** The name of the explicit time variables. */
  //WARNING global mutable state. Changed by addTimeVar. Do not run 2 AxiomaticODESolvers sequentially!
  private var TIMEVAR: Variable = "kyxtime".asVariable

  /** The name of the ODE duration variable. */
  private lazy val DURATION: Variable = "t_".asVariable

  /** The name of the evolution domain time variable 0<=s_<=t_ */
  private lazy val EVOL_DOM_TIME: Variable = "s_".asVariable

  //region The main tactic

  def apply(): DependentPositionTactic = axiomaticSolve()

  def axiomaticSolve(instEnd: Boolean = false): DependentPositionTactic =
      (if (instEnd) "solveEnd" else "solve") by ((pos: Position, s: Sequent) => {
    s.sub(pos) match {
      case Some(Diamond(ODESystem(_, True), _)) =>
        useAt("<> diamond", PosInExpr(1::Nil))(pos) &
        boxAxiomaticSolve(instEnd)(pos ++ PosInExpr(0::Nil)) &
        pushNegation(pos) &
        simplifier(pos)
      case Some(Diamond(ODESystem(_, _), _)) =>
        useAt("<> diamond", PosInExpr(1::Nil))(pos) &
        boxAxiomaticSolve(instEnd)(pos ++ PosInExpr(0::Nil)) &
        pushNegation(pos) &
        useAt("PC10", PosInExpr(1::Nil))(pos ++ PosInExpr(0::1::1::Nil)) &
        simplifier(pos)
      case _ => boxAxiomaticSolve(instEnd)(pos)
    }
  })

  /** Normalize into expected shape for diamond solve, after solving dual box ODE. */
  private def pushNegation: DependentPositionTactic = "ANON" by ((pos: Position, s: Sequent) => {
    s.sub(pos) match {
      case Some(Not(Not(_))) => useAt("!! double negation")(pos)
      case Some(Not(Forall(_, _))) => useAt("!all")(pos) & pushNegation(pos ++ PosInExpr(0::Nil))
      case Some(Not(Imply(_, _))) => useAt("!-> deMorgan")(pos) & pushNegation(pos ++ PosInExpr(1::Nil))
      case Some(Not(And(_, _))) => useAt("!& deMorgan")(pos) & pushNegation(pos ++ PosInExpr(1::Nil))
      case _ => skip
    }
  })

  /** Axiomatic solver for box ODEs. */
  private def boxAxiomaticSolve(instEnd: Boolean = false): DependentPositionTactic = "solve" by ((pos: Position, s: Sequent) => {
    val (ode, q) = s.sub(pos) match {
      case Some(Box(ODESystem(o, qq), _)) => (o, qq)
      case Some(f) => throw BelleUnsupportedFailure("Position " + pos + " does not point to a differential equation, but to " + f.prettyString)
      case None => throw BelleUnsupportedFailure("Position " + pos + " does not point to a differential equation")
    }

    val osize = odeSize(ode)

    //The position of the ODE after introducing all [x_0:=x;] assignments
    val odePosAfterInitialVals = pos ++ PosInExpr(List.fill(osize + 2)(1))
    //The position of the [kyxtime:=...;] assignment after using the DS& axiom.
    val timeAssignmentPos = odePosAfterInitialVals ++ PosInExpr(0 :: 1 :: 1 :: Nil)

    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)

    val assumptions = if (pos.isAnte) s.ante.patch(pos.index0, Nil, 1) else s.ante
    val odeVars = StaticSemantics.boundVars(ode).toSet + DURATION + EVOL_DOM_TIME
    val consts = assumptions.filter(_.isFOL).flatMap(FormulaTools.conjuncts).
      filter(StaticSemantics.freeVars(_).toSet.intersect(odeVars).isEmpty).
      // filter quantified, avoid substitution clash in dI on formulas of the shape (\forall x x>0)'
      filter({ case _: Quantified => false case _ => true}).
      map(SimplifierV3.simpWithDischarge(IndexedSeq[Formula](), _, SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1).
      filterNot(f => f==True || f==False). //@todo improve DI
      reduceOption(And).getOrElse(True)

    val simpSol = simplifier(pos ++ (if (q == True) PosInExpr(0 :: 1 :: Nil) else PosInExpr(0 :: 1 :: 1 :: Nil)))
    val simpEvolDom =
      if (q == True) TactixLibrary.skip //evolution domain constraint is trivial, so simplification is not necessary.
      else if (instEnd) simplifier(pos ++ PosInExpr(0 :: Nil))
      else simplifier(pos ++ PosInExpr(0::1::0::0::1::Nil))

    lazy val allExtract1 = remember("\\forall x_ (p_(x_) -> q_()) -> (\\forall x_ p_(x_) -> q_())".asFormula,
      implyR(1)*2 & allL(-1) & allL(-2) & prop & done, namespace)
    lazy val allExtract2 = remember("\\forall x_ (p_(x_) -> r_(x_)&q_()) -> \\forall x_ (p_(x_)->r_(x_)) ".asFormula,
      implyR(1) & allR(1) & allL(-1) & prop & done, namespace)
    lazy val allExtract3 = remember("p_() & \\forall x_ (r_(x_) -> q_(x_)) -> \\forall x_ (r_(x_) -> q_(x_) & p_())".asFormula,
      implyR(1) & andL(-1) & allR(1) & allL(-2) & prop & done, namespace)

    lazy val imply2 = remember("(p_()->s_()&r_()) -> (p_()->(q_()->r_())->s_())".asFormula, prop & done, namespace)

    //@todo preserve consts when solving in context (requires closing const as last step of DI in context - let fails otherwise)
    val simpConsts: DependentPositionTactic = "ANON" by ((pp: Position, ss: Sequent) =>
      if (consts != True && pos.isTopLevel) ss.sub(pp) match {
        case Some(False) => TactixLibrary.skip
        case Some(_) =>
          val constsPos = if (q == True) PosInExpr(0::1::0::0::1::Nil) else PosInExpr(0::1::0::0::1::1::Nil)
          s.sub(pos) match {
            case Some(Box(ODESystem(_, qq), _)) if polarity > 0 =>
              if (qq == True) useAt(allExtract1)(pos ++ PosInExpr(0::1::0::Nil)) &
                useAt(imply2, PosInExpr(1::Nil))(pos ++ PosInExpr(0::Nil)) &
                useAt(allExtract3, PosInExpr(1::Nil))(pos) &
                //@todo pos is top level, prove that consts are true in context
                andR(pos) <(prop & done, skip)
              else useAt(allExtract2)(pos ++ PosInExpr(0::1::0::Nil))
            case Some(Box(ODESystem(_, qq), _)) if polarity < 0 => skip //@todo
          }
      } else TactixLibrary.skip)

    DebuggingTactics.debug("SOLVE Start", ODE_DEBUGGER) &
      //@todo support the cases we now skip
      (if (consts == True || !pos.isTopLevel || polarity < 0) TactixLibrary.skip else DifferentialTactics.diffInvariant(consts)(pos)) &
      DebuggingTactics.debug("AFTER preserving consts", ODE_DEBUGGER) &
      addTimeVar(pos) &
      DebuggingTactics.debug("AFTER time var", ODE_DEBUGGER) &
      odeSolverPreconds(pos ++ PosInExpr(1 :: Nil)) &
      DebuggingTactics.debug("AFTER precondition check", ODE_DEBUGGER) &
      (cutInSoln(osize)(odePosAfterInitialVals) & DebuggingTactics.debug("Cut in a sol'n", ODE_DEBUGGER)) &
      DebuggingTactics.debug("AFTER cutting in all soln's", ODE_DEBUGGER) &
      simplifyEvolutionDomain(osize)(odePosAfterInitialVals ++ PosInExpr(0 :: 1 :: Nil)) &
      DebuggingTactics.debug("AFTER simplifying evolution domain constraint", ODE_DEBUGGER) &
      (if (polarity > 0) HilbertCalculus.DW(odePosAfterInitialVals)
       else if (polarity < 0) HilbertCalculus.useAt(DerivedAxioms.DWeakeningAnd, PosInExpr(0 :: Nil))(odePosAfterInitialVals)
       else throw AxiomaticODESolverExn("Unable to DW: unknown ODE polarity.")
      ) &
      DebuggingTactics.debug("AFTER DW", ODE_DEBUGGER) &
      simplifyPostCondition(osize)(odePosAfterInitialVals ++ PosInExpr(1 :: Nil)) &
      DebuggingTactics.debug("AFTER simplifying post-condition", ODE_DEBUGGER) &
      //@todo box ODE in succedent: could shortcut with diffWeaken (but user-definable if used or not)
      SaturateTactic(inverseDiffCut(osize)(odePosAfterInitialVals) & DebuggingTactics.debug("did an inverse diff cut", ODE_DEBUGGER)) &
      DebuggingTactics.debug("AFTER all inverse diff cuts", ODE_DEBUGGER) &
      simplifier(odePosAfterInitialVals ++ PosInExpr(0 :: 1 :: Nil)) &
      DebuggingTactics.debug("AFTER simplifying evolution domain 2", ODE_DEBUGGER) &
      RepeatTactic(DifferentialTactics.inverseDiffGhost(odePosAfterInitialVals), osize) &
      DebuggingTactics.assert((s, p) => odeSize(s.apply(p)) == 1, "ODE should only have time.")(odePosAfterInitialVals) &
      DebuggingTactics.debug("AFTER all inverse diff ghosts", ODE_DEBUGGER) &
      HilbertCalculus.useAt("DS& differential equation solution")(odePosAfterInitialVals) &
      DebuggingTactics.debug("AFTER DS&", ODE_DEBUGGER) &
      (HilbertCalculus.assignb(timeAssignmentPos) | HilbertCalculus.assignd(timeAssignmentPos) | Idioms.nil) &
      DebuggingTactics.debug("AFTER box assignment on time", ODE_DEBUGGER) &
      HilbertCalculus.assignb(pos) * (osize + 2) & // all initial vals + time_0=time + time=0
      DebuggingTactics.debug("AFTER inserting initial values", ODE_DEBUGGER) &
      simpConsts(pos ++ PosInExpr(0::1::0::0::1::Nil)) &
      DebuggingTactics.debug("AFTER simplifying consts", ODE_DEBUGGER) &
      (if (q == True && consts == True) TactixLibrary.useAt("->true")(pos ++ PosInExpr(0 :: 1 :: 0 :: 0 :: Nil)) &
        TactixLibrary.useAt("vacuous all quantifier")(pos ++ PosInExpr(0 :: 1 :: 0 :: Nil)) &
        (TactixLibrary.useAt("true->")(pos ++ PosInExpr(0 :: 1 :: Nil))
          | TactixLibrary.useAt("true&")(pos ++ PosInExpr(0 :: 1 :: Nil)))
      else if (instEnd) TactixLibrary.allL("t_".asVariable)(pos ++ PosInExpr(0 :: 1 :: 0 :: Nil)) &
        TactixLibrary.useAt("<= flip")(pos ++ PosInExpr(0 :: 1 :: 0 :: 0 :: 0 :: Nil))
      else TactixLibrary.skip) &
      DebuggingTactics.debug("AFTER handling evolution domain", ODE_DEBUGGER) &
      simpSol & simpEvolDom &
      DebuggingTactics.debug("AFTER final simplification", ODE_DEBUGGER)
  })

  //endregion

  //region Preconditions

   class Cycle extends Exception {}

  private def myFreeVars(term:Term): SetLattice[Variable] = {
    term match {
      /* Hack: ODE solving actually works ok sometimes if semantically free variables are treated as free.
       * If we have something in the linear form expected by DG, then leave it around and see if it solves.
       * some of the case studies use this. */
      case Plus(Times(Number(n),_), e) if n == 0 => StaticSemantics.freeVars(e)
      case e => StaticSemantics.freeVars(e)
    }
  }

  private def dfsLoop(odes: List[AtomicODE], visited: Set[Variable], active: Set[Variable],
                      curr: Variable, acc: List[Variable]): Option[(Set[Variable], List[Variable])] = {
    if (visited.contains(curr)) {
      None
    } else if (acc.contains(curr)) {
      Some(visited + curr, acc)
    } else {
      val currRhs = odes.find(_.xp.x == curr).get.e
      val incoming = odes.filter(ode => myFreeVars(currRhs).contains(ode.xp.x)).map(_.xp.x)
      if (incoming.exists(active.contains)) throw new Cycle
      val (vis, sorted) = incoming.foldLeft[(Set[Variable], List[Variable])]((visited + curr, acc))({case ((vis2, acc2), x) =>
        dfsLoop(odes, vis2, active + curr, x, acc2) match {
          case Some(xx)  => xx
          case _  => (vis2, acc2)
        }
      })
      Some(vis, curr :: sorted)
    }
  }

  def alist(ode: DifferentialProgram): Option[List[AtomicODE] ]= {
    ode match {
      case _: DifferentialProgramConst => None
      case DifferentialProduct(ode1, ode2) =>
        (alist(ode1), alist(ode2)) match {
          case ((_, None)) => None
          case ((None, _)) => None
          case (Some(x), Some(y)) => Some(x ++ y)
        }
      case ode: AtomicODE => Some(List(ode))
    }
  }
  def ofAtoms(atoms:List[AtomicODE]):DifferentialProgram = {
    atoms match {
      case Nil => ???
      case ode::Nil => ode
      case ode::rest => DifferentialProduct(ode, ofAtoms(rest))
    }
  }

  private def dfsOuterLoop(odes: List[AtomicODE], visited: Set[Variable], acc: List[Variable]): Option[(Set[Variable], List[Variable])] = {
    if (visited.size == odes.size) {
      Some(visited, acc)
    } else {
      val curr = odes.find(ode => !visited.contains(ode.xp.x)).get.xp.x
      dfsLoop(odes, Set(), Set(curr), curr, acc) match {
        case None => None
        case Some((vis, a)) => dfsOuterLoop(odes, vis ++ visited, a)
      }
    }
  }

  def dfs(ode: DifferentialProgram): Option[List[Variable]] = {
    try {
      alist(ode) match {
        case Some(atomics) => dfsOuterLoop(atomics, Set(),  Nil).map(_._2) match {
          case None => None
          case Some(vs) =>
            // ODE solving tactic expects kyxtime variable to stay at the end. Let's keep it that way since it never depends on other variables
            if (vs.contains(Variable("kyxtime"))) Some(vs.filter(_ != Variable("kyxtime")) :+ Variable("kyxtime"))
            else Some(vs)
        }
        case None => None
      }
    } catch  {
      case _: Cycle => None
    }
  }

  def sortSubst(dom:Formula, post:Formula, context:DifferentialProgram, ode1:DifferentialProgram, ode2:DifferentialProgram):USubst = USubst(List(
    SubstitutionPair(DifferentialProgramConst("c"), context),
    SubstitutionPair(DifferentialProgramConst("d"), ode1),
    SubstitutionPair(DifferentialProgramConst("e"), ode2),
    SubstitutionPair(UnitPredicational("q", AnyArg), dom),
    SubstitutionPair(UnitPredicational("p", AnyArg), post)))

  def sortAxiomInst(dom:Formula, post:Formula, context:DifferentialProgram, ode1:DifferentialProgram, ode2:DifferentialProgram):Provable = {
    Provable.axioms(", sort")(sortSubst(dom, post, context, ode1,ode2))
  }

  def commSubst(dom:Formula, post:Formula, ode1:DifferentialProgram, ode2:DifferentialProgram):USubst = USubst(List(
    SubstitutionPair(DifferentialProgramConst("c"), ode1),
    SubstitutionPair(DifferentialProgramConst("d"), ode2),
    SubstitutionPair(UnitPredicational("q", AnyArg), dom),
    SubstitutionPair(UnitPredicational("p", AnyArg), post)))

  def commAxiomInst(dom:Formula, post:Formula, ode1:DifferentialProgram, ode2:DifferentialProgram):Provable = {
    Provable.axioms(", commute")(commSubst(dom, post, ode1, ode2))
  }

  def splitODEAt(ode:DifferentialProgram, v:Variable):(List[AtomicODE], List[AtomicODE], List[AtomicODE]) = {
    ode match {
      case DifferentialProduct(AtomicODE(DifferentialSymbol(v2),e), tail) => {
        if (v == v2) {
          (Nil, List(AtomicODE(DifferentialSymbol(v2),e)), alist(tail).get)
        } else {
          splitODEAt(tail, v) match {
            /* If variable already found, add ourselves to the context */
            case (l1, o::l2, l3) => (AtomicODE(DifferentialSymbol(v2),e)::l1, o::l2, l3)
            /* If variable not yet found, add ourselves to the tail */
            case (Nil, Nil, l3) => (Nil, Nil, AtomicODE(DifferentialSymbol(v2),e)::l3)
            /* Should never happen */
            case _ => ???
          }
        }
      }
      case AtomicODE(DifferentialSymbol(v2), e) => {
        if (v == v2) {
          (Nil, List(AtomicODE(DifferentialSymbol(v2), e)), Nil)
        } else {
          (Nil, Nil, List(AtomicODE(DifferentialSymbol(v2), e)))
        }
      }
    }
  }

  /* Produces a tactic that transforms  [ODE & Q]P (at pos) into [sorted_ode & Q]P
  * This works in selection-sort style: At step i, pull the variable whose final position should be i to the end of ODE*/
  def selectionSort(dom:Formula, post:Formula, ode: DifferentialProgram, goal: List[Variable], pos:Position):BelleExpr = {
    val insts =
      goal.foldLeft((ode, TactixLibrary.nil, Nil:List[Provable]))({ case ((ode, e,insts), v) =>
        val (l1, l2, l3) = splitODEAt(ode, v)
        // Already at end - no commuting necessary
        if(l3.isEmpty) {
          (ode, e, insts)
        // Currently at beginning: use regular ODE commute axiom, not contextual ODE commute
        } else if(l1.isEmpty) {
          val (ode2, ode3) = (ofAtoms(l2), ofAtoms(l3))
          val pr = commAxiomInst(dom, post, ode2,ode3)
          val newOde = DifferentialProduct(ode3, ode2)
          (newOde, e, pr::insts)
        // Neither at beginning nor end: use contextual ODE commute axiom.
        } else {
          val (ode1, ode2, ode3) = (ofAtoms(l1), ofAtoms(l2), ofAtoms(l3))
          val pr = sortAxiomInst(dom, post, ode1,ode2,ode3)
          val newOde = DifferentialProduct(ode1, DifferentialProduct(ode3, ode2))
          (newOde, e, pr::insts)
        }
      })._3
    // The above gives us a chain of equivalences on ODES: piece the chain together.
    insts.map(pr => HilbertCalculus.useAt(ElidingProvable(pr), PosInExpr(0::Nil))(pos)).foldLeft(TactixLibrary.nil)((acc, e) => e & acc)// & HilbertCalculus.byUS("<-> reflexive")
  }

  /* Produces a tactic that permutes ODE into canonical ordering or a tacatic that errors if ode contains cycles */
  def makeCanonical(ode: DifferentialProgram, dom: Formula, post: Formula, pos: Position): BelleExpr = {
    dfs(ode) match {
      case None => DebuggingTactics.error("Expected ODE to be linear and in correct order.")
      case Some(ord) => DebuggingTactics.debug("Sorting to " + ord.mkString("::"), ODE_DEBUGGER) & selectionSort(dom, post, ode, ord, pos)
    }
  }

  val odeSolverPreconds: DependentPositionTactic =  TacticFactory.anon ((pos: Position, s: Sequent) => {
    val (ode: DifferentialProgram, dom:Formula, post:Formula) = s.sub(pos) match {
      case Some(Box(ODESystem(o, q), p)) => (o, q, p)
      case sub => throw BelleTacticFailure("Expected [] or <> modality at position " + pos + ", but got " + sub)
    }

    DebuggingTactics.debug("Before Canonicalization") &
    makeCanonical(ode, dom, post, pos) &
    DebuggingTactics.debug("After Canonicalization") &
    StaticSemantics.boundVars(ode).symbols.filter(_.isInstanceOf[DifferentialSymbol]).map({case DifferentialSymbol(v) => v}).
      foldLeft[BelleExpr](Idioms.nil)((a, b) => a & TactixLibrary.discreteGhost(b)(pos))
  })

  //endregion

  //region Setup time variable

  /** Rewrites [{c}]p to [{c, t'=1}]p.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar: DependentPositionTactic = TacticFactory.anon ((pos: Position, s:Sequent) => {
    s.sub(pos ++ PosInExpr(0::Nil)) match {
      case Some(_: DifferentialProgram) => //ok
      case Some(_: ODESystem) => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s.apply(pos)} of type ${s.apply(pos).getClass}.")
    }

    val t = TacticHelper.freshNamedSymbol(TIMEVAR, s)
    TIMEVAR = t //WARNING global state

    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)

    if (polarity > 0) HilbertCalculus.DGC(t, Number(1))(pos) & DLBySubst.assignbExists(Number(0))(pos)
    else if (polarity < 0) HilbertCalculus.DGCa(t, Number(1))(pos) & DLBySubst.assignbAll(Number(0))(pos)
    else throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality in known polarity.")
  })

  //endregion

  //region Cut in solutions

  def cutInSoln(odeSize: Int, diffArg:Term = Variable("kyxtime")): DependentPositionTactic = "cutInSoln" by ((pos: Position, s: Sequent) => {
    val system: ODESystem = s.sub(pos) match {
      case Some(Box(x: ODESystem, _)) => x
    }

    def extract(f: Formula, p: PosInExpr, n: Int): List[(Variable, Term)] =
      if (n == 0) Nil
      else extract(f, p.parent, n-1) :+ (f.sub(p) match { case Some(Box(Assign(v, t: Variable), _)) => t -> v })

    val initialConditions: Map[Variable, Term] = extract(s(pos.top), pos.inExpr.parent, odeSize+1).toMap

    val initIdx = TIMEVAR.index.getOrElse(-1) + 1

    //@note we have to cut one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.

    val solutions = Integrator(initialConditions, Minus(TIMEVAR, Variable(TIMEVAR.name, Some(initIdx))), system)

    val sortedDifferentials = sortAtomicOdes(atomicOdes(system), diffArg).filter(_.xp.x != TIMEVAR).map(_.xp.x)
    val sortedSolutions = solutions.sortWith({case (Equal(a, _), Equal(b, _)) => sortedDifferentials.indexOf(a) < sortedDifferentials.indexOf(b)})

    sortedSolutions.foldRight(nil)((soln, tactic) => cutAndProveFml(soln, odeSize+1)(pos) & tactic)
  })

  /** Augment ODE with formula `cut`, consider context of size `contextSize` when proving with DI. */
  def cutAndProveFml(cut: Formula, contextSize: Int = 0): DependentPositionTactic = "ANON" by ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    val withInitialsPos = pos.topLevel ++ PosInExpr(pos.inExpr.pos.dropRight(contextSize))

    val fact = s.sub(withInitialsPos) match {
      case Some(fml: Formula) =>
        val odePos = PosInExpr(pos.inExpr.pos.takeRight(contextSize))
        val (ctx, modal: Modal) = Context.at(fml, odePos)
        val ODESystem(_, e) = modal.program
        val factFml =
          if (polarity > 0) Imply(ctx(modal.replaceAt(PosInExpr(0::1::Nil), And(e, cut))), fml)
          else Imply(fml, ctx(modal.replaceAt(PosInExpr(0::1::Nil), And(e, cut))))
        TactixLibrary.proveBy(factFml,
          TactixLibrary.implyR(1) & TactixLibrary.dC(cut)(if (polarity > 0) 1 else -1, odePos) <(
            TactixLibrary.close
            ,
            TactixLibrary.cohideR('Rlast) &
              DebuggingTactics.debug("Normalizing", ODE_DEBUGGER) & TactixLibrary.assignb(1)*contextSize &
              DebuggingTactics.debug("diffInd", ODE_DEBUGGER) & DifferentialTactics.diffInd()(1) & DebuggingTactics.done
          )
        )
    }

    TactixLibrary.useAt(fact, PosInExpr((if (polarity > 0) 1 else 0 )::Nil))(withInitialsPos)
  })

  /**
    *
    * @param v A variable occuring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isSolved(v: Variable, system: ODESystem): Boolean = {
    //Variables that don't occur in the ODE are trivially already solved
    //An occurring variable is solved when an evolution domain constraint of the form 'a = ...' exists
    !atomicOdes(system.ode).exists(_.xp.x == v) ||
      FormulaTools.conjuncts(system.constraint).exists({ case Equal(l, _) => l == v case _ => false })
  }

  //endregion

  //region Simplify post-condition and evolution domain constraint

  private def simplifyEvolutionDomain(odeSize: Int) = "simplifyEvolutionDomain" by ((pos: Position, _: Sequent) => {
    lazy val simplFact = remember(
      "p_(f(x_)) & x_=f(x_) <-> p_(x_) & x_=f(x_)".asFormula, TactixLibrary.equivR(1) <(
        TactixLibrary.andL(-1) & TactixLibrary.andR(1) < (TactixLibrary.eqL2R(-2)(1) & TactixLibrary.closeId, TactixLibrary.closeId),
        TactixLibrary.andL(-1) & TactixLibrary.andR(1) < (TactixLibrary.eqR2L(-2)(1) & TactixLibrary.closeId, TactixLibrary.closeId)
        ), namespace)

    val step = "simplifyEvolDomainStep" by ((pp: Position, ss: Sequent) => {
      val subst = (_: Option[TactixLibrary.Subst]) => ss.sub(pp) match {
        case Some(And(p, Equal(x, f))) => RenUSubst(
          ("x_".asVariable, x) ::
            ("p_(.)".asFormula, p.replaceFree(x, DotTerm())) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil)
      }
      TactixLibrary.useAt(simplFact, PosInExpr(1::Nil), subst)(pp)
    })

    (0 until odeSize).map(List.fill(_)(0)).map(i => step(pos ++ PosInExpr(i))).reduceRight[BelleExpr](_ & _)
  })

  def simplifyPostCondition(odeSize: Int): DependentPositionTactic = "simplifyPostCondition" by ((pos: Position, seq: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(seq(pos.top), pos.inExpr)

    lazy val rewrite1 = remember("(q_(f(x_)) -> p_(f(x_))) -> (q_(x_) & x_=f(x_) -> p_(x_))".asFormula,
      TactixLibrary.implyR(1) * 2 & TactixLibrary.andL(-2) & TactixLibrary.eqL2R(-3)(1) &
        TactixLibrary.eqL2R(-3)(-2) & TactixLibrary.prop & TactixLibrary.done, namespace)
    lazy val rewrite2 = remember("(q_(x_) & x_=f(x_)) & p_(x_) -> q_(f(x_)) & p_(f(x_))".asFormula,
      TactixLibrary.implyR(1) & TactixLibrary.andL(-1) * 2 & TactixLibrary.andR(1) &
        OnAll(TactixLibrary.eqR2L(-3)(1) & TactixLibrary.closeId), namespace)
    lazy val rewrite3 = remember("p_() -> (q_() -> p_())".asFormula, TactixLibrary.prop, namespace)

    //@note compute substitution fresh on each step, single pass unification match does not work because q_(x_) before x_=f
    ("simplifyPostConditionStep" by ((pp: Position, ss: Sequent) => {
      val (xx, subst, rewrite) = ss.sub(pp) match {
        case Some(Imply(And(q, Equal(x: Variable, f)), p)) => (x, (_: Option[TactixLibrary.Subst]) => RenUSubst(
          ("x_".asVariable, x) ::
            ("q_(.)".asFormula, q.replaceFree(x, DotTerm())) ::
            ("p_(.)".asFormula, Box(Assign(x, DotTerm()), p).replaceAll(x, "x_".asVariable)) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil), rewrite1)
        case Some(And(And(q, Equal(x: Variable, f)), p)) => (x, (_: Option[TactixLibrary.Subst]) => RenUSubst(
          ("x_".asVariable, x) ::
            ("q_(.)".asFormula, q.replaceFree(x, DotTerm())) ::
            ("p_(.)".asFormula, Box(Assign(x, DotTerm()), p).replaceAll(x, "x_".asVariable)) ::
            ("f(.)".asTerm, f.replaceFree(x, DotTerm())) ::
            Nil), rewrite2)
      }
      DLBySubst.stutter(xx)(pp ++ PosInExpr(1::Nil)) &
      TactixLibrary.useAt(rewrite, if (polarity > 0) PosInExpr(1::Nil) else PosInExpr(0::Nil), subst)(pp) &
      TactixLibrary.assignb(pp ++ PosInExpr(1::Nil))
    }))(pos)*odeSize &
      (if (polarity > 0) TactixLibrary.useAt(rewrite3, PosInExpr(1::Nil))(pos)
       else TactixLibrary.skip) & simplifier(pos)
  })

  //endregion

  //region Inverse diff cuts

  private def inverseDiffCut(odeSize: Int): DependentPositionTactic = "inverseDiffCut" by ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    val withInitialsPos = pos.topLevel ++ PosInExpr(pos.inExpr.pos.dropRight(odeSize+1))
    val fact = s.sub(withInitialsPos) match {
      case Some(fml: Formula) =>
        val odePos = PosInExpr(pos.inExpr.pos.takeRight(odeSize+1))
        val (ctx, modal: Modal) = Context.at(fml, odePos)
        val ODESystem(_, And(e, soln)) = modal.program
        val factFml =
          if (polarity > 0) Imply(ctx(modal.replaceAt(PosInExpr(0::1::Nil), e)), fml)
          else Imply(fml, ctx(modal.replaceAt(PosInExpr(0::1::Nil), e)))
        TactixLibrary.proveBy(factFml,
          TactixLibrary.implyR(1) & TactixLibrary.dC(soln)(if (polarity > 0) -1 else 1, odePos) <(
            TactixLibrary.close
            ,
            TactixLibrary.cohideR('Rlast) &
            DebuggingTactics.debug("Normalizing", ODE_DEBUGGER) & TactixLibrary.assignb(1)*(odeSize+1) &
            DebuggingTactics.debug("diffInd", ODE_DEBUGGER) & DifferentialTactics.diffInd()(1) & DebuggingTactics.done
            )
        )
    }

    TactixLibrary.useAt(fact, PosInExpr((if (polarity > 0) 1 else 0)::Nil))(withInitialsPos)
  })

  //endregion

  private def odeSize(e: Expression): Int = odeSize(e.asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode)
  private def odeSize(ode: DifferentialProgram): Int = ode match {
    case _: DifferentialProgramConst => 1
    case _: AtomicODE => 1
    case x: DifferentialProduct => odeSize(x.left) + odeSize(x.right)
  }

  //region Misc.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)

  //endregion
}
