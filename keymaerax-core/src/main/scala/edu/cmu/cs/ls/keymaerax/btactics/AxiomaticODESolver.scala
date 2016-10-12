/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import TacticFactory._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * An Axiomatic ODE solver.
  * Current Limitations:
  *   * Only works in top-level succedent positions. I think this is only
  *     a limitation imposed by the differential tactics used herein.
  *   * Initial conditions must already exist. Stefan has a work-around
  *     that ghosts in initial conditions already in the diffSolve tactic.
  *   * Brittle when the initial ODE already has a domain constraint.
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  */
object AxiomaticODESolver {
  private val ODE_DEBUGGER = false

  /** The name of the explicit time variables. */
  private val TIMEVAR : String = "kyxtime"

  /** Temporary messages that aren't even necessarily useful to have in verbose ODE debugger mode. */
  private def tmpmsg(s:String) = if(ODE_DEBUGGER) println(s)

  //region The main tactic

  def apply() = axiomaticSolve()

  def axiomaticSolve() = "AxiomaticODESolver" by ((pos:Position, s:Sequent) => {
    val odePos = subPosition(pos, 0::Nil)
    val ode = s.apply(pos).asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode
    val sizeOfTimeExplicitOde = odeSize(ode) + 1

    //The position of the [kyxtime:=...;] assignment after using the DS& axiom.
    val timeAssignmentPos = subPosition(pos, PosInExpr(0::1::1::Nil))
    val isAssignment : Expression => Boolean = (e : Expression) => e match {
      case Box(Assign(_,_), _) => true
      case _ => false
    }

    odeSolverPreconds(pos) &
    DebuggingTactics.debug("AFTER precondition check", ODE_DEBUGGER) &
    addTimeVarIfNecessary(odePos) &
    DebuggingTactics.debug("AFTER time var", ODE_DEBUGGER) &
    assertInitializedTimeVar(odePos) & //@note we leave t'=0*t+1 for now because it's easier to name the position after inverseDiffGhost steps.
    (cutInSoln(pos) & DebuggingTactics.debug("Cut in a sol'n", ODE_DEBUGGER)).* &
    DebuggingTactics.debug("AFTER cutting in all soln's", ODE_DEBUGGER) &
    HilbertCalculus.DW(pos) &
    DebuggingTactics.debug("AFTER DW", ODE_DEBUGGER) &
    simplifyPostCondition(pos) &
    DebuggingTactics.debug("AFTER simplifying post-condition", ODE_DEBUGGER) &
    (inverseDiffCut(pos) & DebuggingTactics.debug("did an inverse diff cut", ODE_DEBUGGER)).* &
    DebuggingTactics.debug("AFTER all inverse diff cuts", ODE_DEBUGGER) &
    RepeatTactic(inverseDiffGhost(pos), sizeOfTimeExplicitOde - 1) &
    DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == 1, "ODE should only have time.")(pos) &
    DebuggingTactics.debug("AFTER all inverse diff ghosts", ODE_DEBUGGER) &
    HilbertCalculus.useAt("DS& differential equation solution")(pos) &
    DebuggingTactics.debug("AFTER DS&", ODE_DEBUGGER) &
    ((DebuggingTactics.assertAt((x:Expression) => s"Should be a boxed assignment: ${x.getClass}", isAssignment)(timeAssignmentPos) &
      HilbertCalculus.assignb(timeAssignmentPos)
     )
     |
      Idioms.nil
    ) &
    DebuggingTactics.debug("AFTER box assignment on time", ODE_DEBUGGER)
  })

  //endregion

  //region Preconditions

  val odeSolverPreconds =  TacticFactory.anon ((pos: Position, s: Sequent) => {
    val modal = s.apply(pos).asInstanceOf[Modal]
    val ODESystem(ode, constraint) = modal.program

    if(modal.isInstanceOf[Diamond])
      throw noDiamondsForNowExn
    else if(!isCanonicallyLinear(ode))
      DebuggingTactics.error("Expected ODE to be linear and in correct order.")
    else if(!anteHasInitConds(s.ante, ode))
      DebuggingTactics.error("Expected sequent to have initial conditions for ODE.")
    else
      Idioms.nil
  })

  //endregion

  //region Setup time variable

  /** Adds a time variable to the ODE if there isn't one already; otherwise, does nothing.
    *
    * @see [[addTimeVar]] */
  val addTimeVarIfNecessary = TacticFactory.anon ((pos: Position, s:Sequent) => s.apply(pos) match {
      case x:DifferentialProgram => addTimeVar(pos)
      case x:ODESystem => addTimeVar(pos)
      case _ => throw AxiomaticODESolverExn(s"Expected DifferentialProgram or ODESystem but found ${s.apply(pos).getClass}")
  })

  val assertInitializedTimeVar = TacticFactory.anon ((pos: Position, s: Sequent) => {
    val timer = s.apply(pos) match {
      case x: ODESystem => Variable(TIMEVAR)
      case x: DifferentialProgram => Variable(TIMEVAR)
      case _ => throw AxiomaticODESolverExn(s"Expected differential program or ode system but found ${s.apply(pos).prettyString}")
    }
    val initialConditions = conditionsToValues(s.ante.flatMap(extractInitialConditions(None)).toList)

    DebuggingTactics.assert(_ => initialConditions.keySet contains timer,
      s"There is no initialCondition for the time variable ${timer}") &
    DebuggingTactics.assert(_ => initialConditions(timer) == Number(0),
      s"The initial condition for ${timer} is non-zero (${initialConditions(timer)})")
  })

  /** Rewrites [{c}]p to [{c, t'=1}]p whenever the system c does not already contain a clock.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar = TacticFactory.anon ((pos: Position, s:Sequent) => {
    s.apply(pos) match {
      case x:DifferentialProgram => //ok
      case x:ODESystem => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s.apply(pos)} of type ${s.apply(pos).getClass}.")
    }

    val modalityPos = parentPosition(pos)
    if(!s.apply(modalityPos).isInstanceOf[Modal])
      throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")

    val t = TacticHelper.freshNamedSymbol(Variable(TIMEVAR), s)

    s.apply(modalityPos) match {
      case Box(_,_) => {
        HilbertCalculus.DGC(t, Number(1))(modalityPos) &
        DLBySubst.assignbExists(Number(0))(modalityPos) &
        DLBySubst.assignEquality(modalityPos)
      }
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  //endregion

  //region Cut in solutions

  val cutInSoln = "cutInSoln" by ((pos: Position, s: Sequent) => {
    assert(s.apply(pos).isInstanceOf[Modal], s"Expected a modality but found ${s.apply(pos).prettyString}")
    val system:ODESystem = s.apply(pos).asInstanceOf[Modal].program match {
      case x:ODESystem => x
      case x:DifferentialProgram => ???
    }

    //@todo constrain to only true initial conditions by passing in Some(ode).
    //@todo I don't think that the extractInitialConditions code picks up a=0 as an initial condtion for x'=v,v'=a. Check this when changing None.
    val initialConditions = s.ante.flatMap(extractInitialConditions(None)).toList

    val nextEqn = sortAtomicOdes(atomicOdes(system))
      .filter(eqn => eqn.xp.x != Variable(TIMEVAR))
      .filter(eqn => isUnsolved(eqn.xp.x, system))
      .head

    tmpmsg(s"next equation to integrate and cut: ${nextEqn.prettyString}")

    //@todo switch completely to the new integrator, so that this is a single tactic instead of a saturated tactic.
    val solnToCut =
      Integrator(conditionsToValues(initialConditions), Variable(TIMEVAR), system).find(eq => eq.left == nextEqn.xp.x)
        .getOrElse(throw new Exception(s"Could not get integrated value for ${nextEqn.xp.x} using new integration logic."))

    tmpmsg(s"Solution for ${nextEqn.prettyString} is ${solnToCut}")

    //@note we have to cut one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.
    s.apply(pos) match {
      case Box(ode, postcond) => {
        DifferentialTactics.diffCut(solnToCut)(pos) <(
          Idioms.nil,
          DebuggingTactics.debug("Doing diffInd on ", ODE_DEBUGGER) & DifferentialTactics.diffInd()(pos) & DebuggingTactics.done
        )
      }
      case Diamond(ode, postcond) => throw noDiamondsForNowExn
    }
  })

  /**
    * @param ode
    * @return The list of atomic differential equations occurring in the differential program.
    * @author Nathan Fulton
    */
  private def odeConstraints(ode : Program) : List[Formula] = ode match {
    case AtomicODE(x,e)                   => Nil
    case ODESystem(ode, constraint)       => constraint :: Nil
    case DifferentialProduct(left, right) => odeConstraints(left) ++ odeConstraints(right)
    case _                                => throw AxiomaticODESolverExn("Expected AtomicODE, ODESystem, or DifferentialProduct.") //@todo what about other differential programs?
  }

  /**
    *
    * @param v A variable occuring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isUnsolved(v : Variable, system : ODESystem) = {
    val odes = atomicOdes(system.ode)
    if(odes.find(_.xp.x.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
    //In non-special cases, check for a = evolution domain constraint in the ode.
    else {
      val vConstraints = odeConstraints(system).flatMap(decomposeAnds).find(_ match {
        case Equal(l, r) => l.equals(v)
        case _ => false
      })
      vConstraints.isEmpty
    }
  }

  //endregion

  //region diffCut lower bound on time

  /** Adds t>=0 to the differential equation's domain constraint.
    * @todo Why is this necessary? It's not included in the paper proof. */
  val cutInTimeLB = "cutInTimeLB" by ((pos: Position, s: Sequent) => {
    assert(s.apply(pos).isInstanceOf[Modal], s"Expected modality at position ${pos} of ${s.prettyString}")
    assert(s.apply(pos).asInstanceOf[Modal].program.isInstanceOf[ODESystem], s"Expected modality to contain ODE System but it did not in ${s(pos)}")

    val system = s.apply(pos).asInstanceOf[Modal].program.asInstanceOf[ODESystem]

    val lowerBound = Number(0) //@todo check that this is actually the lower bound. Lower bound could be symbolic.
    val timer = Variable(TIMEVAR)

    //@todo this won't work in the case where we cut in our own time until Stefan's code for isntantiating exisentials is added in...
    s.apply(pos).asInstanceOf[Modal] match {
      case Box(_,_) => TactixLibrary.diffCut(GreaterEqual(timer, lowerBound))(pos) <(Idioms.nil, TactixLibrary.diffInd()(pos) & DebuggingTactics.done)
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  //endregion

  //region Simplify post-condition

  val simplifyPostCondition = "simplifyPostCondition" by ((pos: Position, s: Sequent) => {
    val modality = s.apply(pos).asInstanceOf[Modal]
    val Box(ode, Imply(evolutionDomain, originalConclusion)) = modality

    val newConclusion = simplifiedConclusion(evolutionDomain, originalConclusion)
    val implication = Imply(newConclusion, modality.child)

    tmpmsg(s"The implication ${implication.prettyString} needs to be valid because we need to co-hide all other formulas for CMon.")
    tmpmsg(s"And modality is ${s.apply(pos).prettyString}")

    //@todo support non-arithmetic post-conditions such as [ODE][more]arith
    if(!implication.isFOL)
      throw new AxiomaticODESolverExn("Could not solve the ODE axiomatically because the post-condition is non-arithmetic.")

    TactixLibrary.cutAt(newConclusion)(subPosition(pos, PosInExpr(1::Nil))) <(
      Idioms.nil
      ,
      SequentCalculus.cohideR('Rlast) & TactixLibrary.CMon(PosInExpr(1::Nil)) & (TactixLibrary.QE | TactixLibrary.close) & DebuggingTactics.done
    )
  })

  private def simplifiedConclusion(evolutionDomain: Formula, originalConclusion: Formula): Formula = {
    val fvs = StaticSemantics.freeVars(originalConclusion)
    val varsToReplace : Map[Variable, Term] = conditionsToValues(extractInitialConditions(None)(evolutionDomain)).filterKeys(fvs.contains)

    varsToReplace.foldLeft(originalConclusion)(
      (currentFormula, nextPair) => SubstitutionHelper.replaceFree(currentFormula)(nextPair._1, nextPair._2)
    )
  }

  @deprecated("Move this to a centralized location for ProveAs stuff", "4.2b2")
  private def clearProveAsScope(lemmaName: String) = new DependentTactic("clearProveAsScope") {
    override def computeExpr(p:Provable) = {
      //Silently succeed if the lemma does not yet exist.
      if(LemmaDBFactory.lemmaDB.contains(lemmaName))
        LemmaDBFactory.lemmaDB.remove(lemmaName)
      Idioms.nil
    }
  }

  //endregion

  //region Inverse diff cuts

  val inverseDiffCut = "inverseDiffCut" by ((pos: Position, s: Sequent) => {
    val f: Modal = s.apply(pos).asInstanceOf[Modal]
    val ODESystem(ode, constraint) = f.program
    val p = f.child

    constraint match {
      case And(leftConstriant, nextConstraint) if(isPartOfSoln(ode, nextConstraint)) => f match {
        case Box(_, _) => {
          HilbertCalculus.useExpansionAt("DC differential cut")(pos) <(
            Idioms.nil, /* Branch with no ev dom contraint */
            DifferentialTactics.diffInd()(1) & DebuggingTactics.done /* Show precond of diff cut */
            )
        }
        case Diamond(_,_) => throw noDiamondsForNowExn
      }
      case _ => Idioms.nil
    }
  })

  /** Returns true iff f is part of the cut-in solution for the ODE. */
  private def isPartOfSoln(ode: DifferentialProgram, f: Formula): Boolean = f match {
    case Equal(t1, t2) => atomicOdes(ode).exists(a => a.xp.x == t1 || a.xp.x == t2)
    case _ => false
  }

  //endregion

  //region Inverse diff ghosts

  /**
    * Removes the left-most DE from a system of ODEs:
    * {{{
    *   [v'=a,t'=1 & q]p
    *   ---------------------- inserverDiffGhost
    *   [x'=v,v'=a,t'=1 & q]p
    * }}}
    */
  val inverseDiffGhost = "inverseDiffGhost" by ((pos: Position, s: Sequent) => {
    val f: Modal = s.apply(pos).asInstanceOf[Modal]
    val ODESystem(ode, constraint) = f.program
    val p = f.child

    ode match {
      case ode:DifferentialProduct => {
        val y_DE = firstODE(ode)    //The left-most ODE in the system matching the pattern y_' = a(|y_|)*y_ + b(|y_|).

        /* Note: Constructing our own substitution because the default substitution seems to get at least g(||) wrong. */
        def subst(r: RenUSubst) = {
          if(ODE_DEBUGGER) println("[inverseDiffGhost] input to subst:    " + r)
          val renaming =
            RenUSubst(URename("y_".asTerm.asInstanceOf[Variable], y_DE.xp.x))

          val result = renaming ++
            RenUSubst(USubst(
              "a(||)".asTerm    ~> renaming(y_DE.e) ::
              "q(|y_|)".asFormula ~> r.substitution("q(|y_|)".asFormula) ::
              DifferentialProgramConst("c", Except("y_".asVariable)) ~> r(DifferentialProgramConst("c", Except("y_".asVariable))) ::
              "p(|y_|)".asFormula ~> r.substitution("p(|y_|)".asFormula) ::
              Nil))

          if(ODE_DEBUGGER) println("[inverseDiffGhost] output from subst: " + result);
          result
        }

        f match {
          case Box(_,_) => {
            val axiomName = "DG inverse differential ghost implicational"

            //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
            TactixLibrary.cut(Forall(y_DE.xp.x::Nil, f)) <(
              HilbertCalculus.useAt("all eliminate")('Llast) & TactixLibrary.close & DebuggingTactics.done
              ,
              TactixLibrary.hide(pos) &
              DebuggingTactics.debug(s"[inverseDiffGhost] Trying to eliminate ${y_DE} from the ODE via an application of ${axiomName}.", ODE_DEBUGGER) &
              HilbertCalculus.useExpansionAt(axiomName, ((s:RenUSubst) => subst(s)))(pos)
            ) &
            DebuggingTactics.assertProvableSize(1) &
            DebuggingTactics.debug(s"[inverseDiffGhost] Finished trying to eliminate ${y_DE} from the ODE.", ODE_DEBUGGER) &
            DebuggingTactics.assert((s,p) => odeSize(s.apply(p)) == odeSize(ode)-1, "[inverseDiffGhost] Size of ODE should have decreased by one after an inverse diff ghost step.")(pos)
          }
          case Diamond(_,_) => throw noDiamondsForNowExn
        }
      }
      case _ => Idioms.nil
    }
  })

  private def firstODE(ode: DifferentialProduct):AtomicODE = ode.left match {
    case pi:DifferentialProduct => firstODE(pi)
    case l:AtomicODE => l
    case _ => ???
  }

  private def secondODE(ode: DifferentialProduct):AtomicODE = ode.left match {
    case pi:DifferentialProduct => secondODE(pi)
    case l:AtomicODE => ode.right match {
      case pi:DifferentialProduct => firstODE(pi)
      case r:AtomicODE => r
      case _ => ???
    }
  }

  private def odeSize(e: Expression): Int = odeSize(e.asInstanceOf[Modal].program.asInstanceOf[ODESystem].ode)
  private def odeSize(ode: DifferentialProgram): Int = ode match {
    case x:DifferentialProgramConst => 1
    case x:AtomicODE => 1
    case x:DifferentialProduct => odeSize(x.left) + odeSize(x.right)
  }

  //endregion

  //region Misc.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
  val noDiamondsForNowExn = AxiomaticODESolverExn("No diamonds for now.")

  def parentPosition(pos: Position): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.parent)
    else SuccPosition(pos.checkSucc.top, pos.inExpr.parent)

  def subPosition(pos: Position, sub: PosInExpr): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr ++ sub)
    else SuccPosition(pos.checkSucc.top, pos.inExpr ++ sub)
  def subPosition(pos: Position, sub: List[Int]): Position = subPosition(pos, PosInExpr(sub))

  //endregion
}
