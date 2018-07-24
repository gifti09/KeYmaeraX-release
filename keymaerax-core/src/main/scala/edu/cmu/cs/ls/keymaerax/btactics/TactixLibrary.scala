/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticIndex.TacticRecursors
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import org.apache.logging.log4j.scala.Logger

import scala.collection.immutable.{List, _}

/**
  * Tactix: Main tactic library with simple interface.
  * This library features all main tactics for the most common cases.
  *
  * For tactics implementing built-in rules such as sequent proof rules,
  * elaborate documentation can be found in the [[edu.cmu.cs.ls.keymaerax.core.Rule prover kernel]].
  *
  * Main search tactics that combine numerous other tactics for automation purposes include:
  *   - [[TactixLibrary.master]] automatic proof search
  *   - [[TactixLibrary.auto]] automatic proof search if that successfully proves the given property
  *   - [[TactixLibrary.normalize]] normalize to sequent normal form
  *   - [[TactixLibrary.unfoldProgramNormalize]] normalize to sequent normal form, avoiding unnecessary branching
  *   - [[TactixLibrary.prop]] propositional logic proving
  *   - [[TactixLibrary.QE]] prove real arithmetic
  *   - [[TactixLibrary.ODE]] proving properties of differential equations
  *   - [[TactixLibrary.step]] performs one canonical simplifying proof step
  *   - [[TactixLibrary.chase]] chase the given formula away by automatic reduction proofs
  *
  * The tactic library also includes individual proof calculi:
  *   - [[HilbertCalculus]]: Hilbert Calculus for differential dynamic logic.
  *   - [[SequentCalculus]]: Sequent Calculus for propositional and first-order logic.
  *   - [[UnifyUSCalculus]]: Automatic unification-based Uniform Substitution Calculus with indexing.
  *
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
  * @see [[HilbertCalculus]]
  * @see [[SequentCalculus]]
  * @see [[UnifyUSCalculus]]
  * @see [[DerivedAxioms]]
  * @see [[AxiomInfo]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
  * @see [[ToolProvider]]
  */
object TactixLibrary extends HilbertCalculus with SequentCalculus {
  import Generator.Generator

  private val logger = Logger(getClass) //@note instead of "with Logging" to avoid cyclic dependencies

  /** Default generator for loop invariants and differential invariants to use.
    * @see [[InvariantGenerator]] */
  var invGenerator: Generator[Formula] = FixedGenerator(Nil)

  /** step: one canonical simplifying proof step at the indicated formula/term position (unless @invariant etc needed) */
  val step          : DependentPositionTactic = "step" by ((pos: Position) =>
    //@note AxiomIndex (basis for HilbertCalculus.stepAt) hands out assignment axioms, but those fail in front of an ODE -> try assignb if that happens
    (if (pos.isTopLevel) stepAt(sequentStepIndex(pos.isAnte)(_))(pos)
     else HilbertCalculus.stepAt(pos))
    | assignb(pos))

  /** Normalize to sequent form. Keeps branching factor of [[tacticChase]] restricted to [[orL]], [[implyL]], [[equivL]], [[andR]], and [[equivR]]. */
  lazy val normalize: BelleExpr = "normalize" by normalize(orL, implyL, equivL, andR, equivR)
  /** Normalize to sequent form. Keeps branching factor of [[tacticChase]] restricted to `beta` rules. */
  def normalize(beta: AtPosition[_ <: BelleExpr]*): BelleExpr = "ANON" by tacticChase()(notL::andL::notR::implyR::orR::allR::existsL::step::ProofRuleTactics.closeTrue::ProofRuleTactics.closeFalse::Nil ++ beta:_*)

  /** Follow program structure when normalizing but avoid branching in typical safety problems (splits andR but nothing else). Keeps branching factor of [[tacticChase]] restricted to [[andR]]. */
  val unfoldProgramNormalize: BelleExpr = "unfold" by normalize(andR)

  /** Exhaustively (depth-first) apply tactics from the tactic index, restricted to the tactics in `restrictTo`, to chase away.
    * Unlike [[chase]], tacticChase will use propositional proof rules and possibly branch
    * @see [[chase]] */
  def tacticChase(tacticIndex: TacticIndex = new DefaultTacticIndex)(restrictTo: AtPosition[_ <: BelleExpr]*): BelleExpr = "ANON" by ((seq: Sequent) => {
    val restrictions = restrictTo.toList

    /** Apply the canonical tactic for the formula at position `pos`; exhaustively depth-first search on resulting other formulas */
    def atPos(except: Option[Position]): DependentPositionTactic = "ANON" by ((pos: Position, s: Sequent) => {
      if (except.contains(pos)) skip
      else s.sub(pos) match {
        case Some(fml) if pos.isAnte && s.succ.contains(fml) => close(pos.checkAnte.top, SuccPos(s.succ.indexOf(fml))) & done
        case Some(fml) if pos.isSucc && s.ante.contains(fml) => close(AntePos(s.ante.indexOf(fml)), pos.checkSucc.top) & done
        case Some(fml) =>
          tacticIndex.tacticFor(fml, restrictions) match {
            case (Some(t), _) if pos.isAnte => applyAndRecurse(t, pos, s)
            case (_, Some(t)) if pos.isSucc => applyAndRecurse(t, pos, s)
            case (None, _) if pos.isAnte => skip
            case (_, None) if pos.isSucc => skip
          }
        case _ => skip
      }
    })

    /** Apply `atPos` at the specified position, or search for the expected formula if it cannot be found there. */
    def atOrSearch(p: PositionLocator): BelleExpr = atPos(None)(p) | (p match {
      case Fixed(pos, Some(fml), exact) if pos.isAnte => atPos(Some(pos))(Find.FindL(0, Some(fml), exact=exact)) | skip
      case Fixed(pos, Some(fml), exact) if pos.isSucc => atPos(Some(pos))(Find.FindR(0, Some(fml), exact=exact)) | skip
      case _ => skip
    })

    /** Do all the tactics of a branch in sequence. */
    def applyBranchRecursor(rec: TacticIndex.Branch): BelleExpr =
      //@note onAll tries on too many branches, but skip in atOrSearch compensates for this
      rec.map(r => onAll(atOrSearch(r))).reduce(_&_)

    /** Turn branches (if any) into a branching tactic. */
    def applyRecursor(rec: TacticIndex.Branches): BelleExpr = rec match {
      case Nil => skip
      case r::Nil => onAll(applyBranchRecursor(r))
      case r => DebuggingTactics.assertProvableSize(r.length) & BranchTactic(r.map(applyBranchRecursor))
    }

    /** Execute `t` at pos, read tactic recursors and schedule followup tactics. */
    def applyAndRecurse(t: AtPosition[_ <: BelleExpr], pos: Position, s: Sequent): BelleExpr = {
      val recursors = tacticIndex.tacticRecursors(t)
      if (recursors.nonEmpty) t(new Fixed(pos)) & (done | recursors.map(r =>
        DebuggingTactics.assertOnAll(_ != s ||
          //@note allow recursing on subposition after no-op steps that supply recursors
          r(s, pos).exists(_.exists({ case Fixed(pp, _, _) => !pp.isTopLevel && pp != pos case _ => false })), "Stopping to recurse on unchanged sequent") &
        applyRecursor(r(s, pos))
      ).reduce(_&_))

      else t(new Fixed(pos))
    }

    //@note Execute on formulas in order of sequent; might be useful to sort according to some tactic priority.
    seq.ante.zipWithIndex.map({ case (fml, i) => onAll(atPos(None)(AntePosition.base0(i), fml) | atPos(Some(AntePosition.base0(i)))('L, fml))}).reduceRightOption[BelleExpr](_&_).getOrElse(skip) &
    seq.succ.zipWithIndex.map({ case (fml, i) => onAll(atPos(None)(SuccPosition.base0(i), fml) | atPos(Some(SuccPosition.base0(i)))('R, fml))}).reduceRightOption[BelleExpr](_&_).getOrElse(skip)
  })

  val prop: BelleExpr = "prop" by tacticChase()(notL, andL, orL, implyL, equivL, notR, implyR, orR, andR, equivR,
                                                ProofRuleTactics.closeTrue, ProofRuleTactics.closeFalse)

  /** Master/auto implementation with tactic `loop` for nondeterministic repetition and `odeR` for
    * differential equations in the succedent.
    * `keepQEFalse` indicates whether or not QE results "false" at the proof leaves should be kept or undone. */
  def master(loop: AtPosition[_ <: BelleExpr], odeR: AtPosition[_ <: BelleExpr],
             keepQEFalse: Boolean): BelleExpr = "ANON" by {
    /** Create a tactic index that hands out loop tactics and configurable ODE tactics. */
    val createAutoTacticIndex = new DefaultTacticIndex {
      override def tacticRecursors(tactic: BelleExpr): TacticRecursors =
        if (tactic == loop) {
          //@todo positions? what to expect there?
          ((_: Sequent, p: Position) => (new Fixed(p) :: Nil) :: (new Fixed(p) :: Nil) :: (new Fixed(p) :: Nil) :: Nil) :: Nil
        } else if (tactic == odeR) {
          ((_: Sequent, p: Position) => (new Fixed(p)::Nil)::Nil) :: Nil
        } else super.tacticRecursors(tactic)
      override def tacticsFor(expr: Expression): (List[AtPosition[_ <: BelleExpr]], List[AtPosition[_ <: BelleExpr]]) = expr match {
        case Box(_: Loop, _) => (Nil, loop::Nil)
        case Box(_: ODESystem, _) => (TactixLibrary.solve::Nil, odeR::Nil)
        case _ => super.tacticsFor(expr)
      }
    }

    OnAll(close |
      SaturateTactic(OnAll(tacticChase(createAutoTacticIndex)(notL, andL, notR, implyR, orR, allR,
        TacticIndex.allLStutter, existsL, TacticIndex.existsRStutter, step, orL,
        implyL, equivL, ProofRuleTactics.closeTrue, ProofRuleTactics.closeFalse,
        andR, equivR, loop, odeR, solve))) & //@note repeat, because step is sometimes unstable and therefore recursor doesn't work reliably
        OnAll(SaturateTactic(exhaustiveEqL2R('L)) & ?(QE & (if (keepQEFalse) nil else done))))
  }

  /** master: master tactic that tries hard to prove whatever it could. `keepQEFalse` indicates whether or not a
    * result `false` of a QE step at the leaves is kept or undone (i.e., reverted to the QE input sequent).
    * @see [[auto]] */
  def master(gen: Generator[Formula] = InvariantGenerator.defaultInvariantGenerator,
             keepQEFalse: Boolean=true): BelleExpr = "master" by {
    def endODE: DependentPositionTactic = "ANON" by ((pos: Position, seq: Sequent) => {
      ODE(pos) & ?(allR(pos) & implyR(pos)*2 & allL(Variable("s_"), Variable("t_"))('Llast) & auto & done)
    })
    master(loopauto(gen), endODE, keepQEFalse)
  }

  /** auto: automatically try hard to prove the current goal if that succeeds.
    * @see [[master]] */
  def auto: BelleExpr = "auto" by master(loopauto(InvariantGenerator.loopInvariantGenerator), ODE, keepQEFalse=true) & done

  /*******************************************************************
    * unification and matching based auto-tactics
 *
    * @see [[UnifyUSCalculus]]
    *******************************************************************/

//  /** US: uniform substitution ([[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule USubst]])
//    * @see [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]]
//    * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
//    */
//  def US(subst: USubst, origin: Sequent): BuiltInTactic = ProofRuleTactics.US(subst, origin)

  // conditional tactics

  /** Call/label the current proof branch by the given label s.
    * @see [[Idioms.<()]]
    * @see [[sublabel()]]
    * @see [[BelleLabels]]
    */
  def label(s: BelleLabel): BelleExpr = LabelBranch(s)

  /** Call/label the current proof branch by the top-level label s.
    *
    * @see [[Idioms.<()]]
    * @see [[sublabel()]]
    */
  def label(s: String): BelleExpr = label(BelleTopLevelLabel(s))

  /** Mark the current proof branch and all subbranches s
    *
    * @see [[label()]]
    */
  def sublabel(s: String): BelleExpr = skip //LabelBranch(BelleSubLabel(???, s))

  // modalities

  /** discreteGhost: introduces a discrete ghost called `ghost` defined as term `t`; if `ghost` is None the tactic chooses a name by inspecting `t`.
    * @example{{{
    *         |- [y_0:=y;]x>0
    *         ----------------discreteGhost("y".asTerm)(1)
    *         |- x>0
    * }}}
    * @example{{{
    *         |- [z:=2;][y:=5;]x>0
    *         ---------------------discreteGhost("0".asTerm, Some("y".asVariable))(1, 1::Nil)
    *         |- [z:=2;]x>0
    * }}}
    * @param t The ghost's initial value.
    * @param ghost The new ghost variable. If None, the tactic chooses a name by inspecting t (must be a variable then).
    * @incontext
    */
  def discreteGhost(t: Term, ghost: Option[Variable] = None): DependentPositionTactic = DLBySubst.discreteGhost(t, ghost)

  /** abstractionb: turns '[a]p' into \forall BV(a) p by universally quantifying over all variables modified in `a`.
    * Returns a tactic to abstract a box modality to a formula that quantifies over the bound variables in the program
    * of that modality.
    * @example{{{
    *           |- \forall x x>0
    *         ------------------abstractionb(1)
    *           |- [x:=2;]x>0
    * }}}
    * @example{{{
    *           |- x>0 & z=1 -> [z:=y;]\forall x x>0
    *         --------------------------------------abstractionb(1, 1::1::Nil)
    *           |- x>0 & z=1 -> [z:=y;][x:=2;]x>0
    * }}}
    * @example{{{
    *           |- x>0
    *         ---------------abstractionb(1)
    *           |- [y:=2;]x>0
    * }}}
    */
  lazy val abstractionb       : DependentPositionTactic = DLBySubst.abstractionb

  /** 'position' tactic t with universal abstraction at the same position afterwards
    * @see [[abstractionb]] */
  def withAbstraction(t: AtPosition[_ <: BelleExpr]): DependentPositionTactic = new DependentPositionTactic("with abstraction") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isTopLevel, "with abstraction only at top-level")
        sequent(pos.checkTop) match {
          case Box(a, p) =>
            t(pos) & abstractionb(pos) & (if (pos.isSucc) SaturateTactic(allR(pos)) partial else skip)
          case Diamond(a, p) if pos.isAnte => ???
        }
      }
    }
  }

  /** loop: prove a property of a loop by induction with the given loop invariant (hybrid systems)
    * Wipes conditions that contain bound variables of the loop.
    * {{{
    *   use:                        init:        step:
    *   I, G\BV(a) |- p, D\BV(a)    G |- I, D    I, G\BV(a) |- [a]p, D\BV(a)
    *   --------------------------------------------------------------------
    *   G |- [{a}*]p, D
    * }}}
    *
    * @example{{{
    *   use:          init:         step:
    *   x>1 |- x>0    x>2 |- x>1    x>1 |- [x:=x+1;]x>1
    *   ------------------------------------------------I("x>1".asFormula)(1)
    *   x>2 |- [{x:=x+1;}*]x>0
    * }}}
    * @example{{{
    *   use:               init:              step:
    *   x>1, y>0 |- x>0    x>2, y>0 |- x>1    x>1, y>0 |- [x:=x+y;]x>1
    *   ---------------------------------------------------------------I("x>1".asFormula)(1)
    *   x>2, y>0 |- [{x:=x+y;}*]x>0
    * }}}
    * @param invariant The loop invariant `I`.
    * @note Currently uses I induction axiom, which is unsound for hybrid games.
    */
  def loop(invariant : Formula)  : DependentPositionTactic = DLBySubst.loop(invariant)
  /** loop=I: prove a property of a loop by induction with the given loop invariant (hybrid systems)
    * @see [[loop()]]
    */
  def I(invariant: Formula)      : DependentPositionTactic = loop(invariant)
  /** loop: prove a property of a loop by induction, if the given invariant generator finds a loop invariant
    * @see [[loop(Formula)]] */
  def loop(gen: Generator[Formula]): DependentPositionTactic = new DependentPositionTactic("I gen") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = loop(nextOrElse(gen(sequent, pos).iterator,
        throw new BelleThrowable("Unable to generate an invariant for " + sequent(pos.checkTop) + " at position " + pos)))(pos)
      private def nextOrElse[A](it: Iterator[A], otherwise: => A) = if (it.hasNext) it.next else otherwise
    }
  }
  /** loop: prove a property of a loop automatically by induction, trying hard to generate loop invariants.
    * @see [[loop(Formula)]] */
  def loopauto(gen: Generator[Formula] = InvariantGenerator.loopInvariantGenerator): DependentPositionTactic =
      "loopauto" by ((pos: Position, seq: Sequent) => {
    //@hack invGenerator collects invariant annotation during parsing; prefer those over the ones generated by gen
    (invGenerator, seq.sub(pos)) match {
      case (cgen: ConfigurableGenerator[Formula], Some(Box(prg@Loop(_), _))) if cgen.products.contains(prg) =>
        logger.debug("LoopAuto uses loop with annotated invariant")
        //@note bypass all other invariant generators except the annotated invariants, pass on to loop
        ChooseSome(
          () => try {
            invGenerator(seq, pos).iterator
          } catch {
            case err: Exception =>
              logger.warn("ChooseSome: error listing options " + err, err)
              List[Formula]().iterator
          },
          (inv: Formula) => loop(inv)(pos) & onAll(auto) & done
        )
      case _ =>
        logger.debug("LoopAuto with loopPostMaster for typical hybrid models plus fallback invariant generator")
        loopPostMaster(gen)(pos) & done |
          ChooseSome(
            () => try {
              gen(seq, pos).iterator
            } catch {
              case err: Exception =>
                logger.warn("ChooseSome: error listing options " + err, err)
                List[Formula]().iterator
            },
            (inv: Formula) => loop(inv)(pos) & onAll(auto) & done
          )
    }
  })

  /** loopSR: cleverly prove a property of a loop automatically by induction, trying hard to generate loop invariants.
    * Uses [[SearchAndRescueAgain]] to avoid repetitive proving.
    * @see [[loopauto]]
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    *      Example 32. */
  def loopSR(gen: Generator[Formula]): DependentPositionTactic = InvariantProvers.loopSR(gen)
  /** loopPostMaster: search-and-rescue style automatic loop induction based on successive generator gen.
    * Uses [[SearchAndRescueAgain]] to avoid repetitive proving.
    * Present implementation needs differential equations to occur somewhere within the loop.
    * @author Andre Platzer
    * @author Stefan Mitsch
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    *      Example 32. */
  def loopPostMaster(gen: Generator[Formula]): DependentPositionTactic = InvariantProvers.loopPostMaster(gen)

  /** throughout: prove a property of a loop by induction with the given loop invariant (hybrid systems) that
    * holds throughout the steps of the loop body.
    * Wipes conditions that contain bound variables of the loop.
    * {{{
    *   use:                      init:        steps:
    *   I, G_cnst |- p, D_cnst    G |- I, D    I, G_cnst |- [a]I,    D_cnst
    *                                          I, G_cnst |- [b;c;]I, D_cnst
    *                                          I, G_cnst |- [d;]I,   D_cnst
    *   -------------------------------------------------------------------
    *   G |- [{a;{b;c;}d}*]p, D
    * }}}
    */
  def throughout(invariant: Formula): DependentPositionTactic = DLBySubst.throughout(invariant)

  /**
    * Loop convergence: prove a diamond property of a loop by induction with a variant for progress.
    * {{{
    *   init:                       use:                         step:
    *   G |- exists v. J(v), D    v<=0, J(v), consts |- p    v>0, J(v), consts |- <a>J(v-1)
    *   --------------------------------------------------------------------------------------------
    *   G |- <{a}*>p, D
    * }}}
    * @param variant The variant property or convergence property in terms of new variable `v`.
    * @example The variant J(v) ~> (v = z) is specified as v=="v".asVariable, variant == "v = z".asFormula
    */
  def con(v: Variable, variant: Formula, pre: BelleExpr = SaturateTactic(alphaRule)): DependentPositionWithAppliedInputTactic = DLBySubst.con(v, variant, pre)


  // differential equations

  /** ODE: try to prove a property of a differential equation automatically.
    *
    * @see [[solve]]
    * @todo @see [[dC]]
    * @see [[dI]]
    * @see [[diffInvariant]]
    * @see [[dW]]
    * @see [[openDiffInd]]
    * @see [[dG]]
    */
  lazy val ODE: DependentPositionTactic = "ODE" by ((pos: Position) => {
    if (ToolProvider.qeTool(Some("Mathematica")).isDefined) DifferentialTactics.fastODE(pos)
    else DifferentialTactics.ODE(pos)
  })

  /**
    * Attempts to prove ODE property as an invariant of the ODE directly [LICS'18]
    * G |- P    P |- [x'=f(x)&Q]P
    * ---
    * G |- [x'=f(x)&Q]P
    * (Default behavior: fast (but incomplete) version, no solving attempted)
    **/
  lazy val odeInvariant: DependentPositionTactic = DifferentialTactics.odeInvariant(false)

  /**
    * Attemppts to prove ODE property by asking for an automatically generated invariant C from Pegasus, i.e.,
    *
    * G |- C  C |- [x'=f(x)&Q]C C |- P
    * ---
    * G |- [x'=f(x)&Q]P
    *
    * (fast version, no solving attempted)
    */
  lazy val odeInvariantAuto: DependentPositionTactic = DifferentialTactics.odeInvariantAuto

  /** DG/DA differential ghosts that are generated automatically to prove differential equations.
    *
    * @see [[dG]] */
  lazy val DGauto: DependentPositionTactic = DifferentialTactics.DGauto

  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`.
    * Similarly, `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (\forall 0<=s<=t q(solution(s)) -> [x:=solution(t)]p(x))`. */
  lazy val solve: DependentPositionTactic = AxiomaticODESolver.axiomaticSolve(instEnd = false)

  /** diffSolve with evolution domain check at duration end: solve `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)`.
    * Similarly, `[x'=f(x)&q(x)]p(x)` turns to `\forall t>=0 (q(solution(t)) -> [x:=solution(t)]p(x))`. */
  lazy val solveEnd: DependentPositionTactic = AxiomaticODESolver.axiomaticSolve(instEnd = true)

  /** DW: Differential Weakening uses evolution domain constraint so `[{x'=f(x)&q(x)}]p(x)` reduces to `\forall x (q(x)->p(x))`.
    * @note FV(post)/\BV(x'=f(x)) subseteq FV(q(x)) usually required to have a chance to succeed. */
  lazy val dW         : DependentPositionTactic = DifferentialTactics.diffWeaken
  /** DC: Differential Cut a new invariant, use old(x) to refer to initial values of variable x.
    * Use special function old(.) to introduce a discrete ghost for the starting value of a variable that can be
    * used in the evolution domain constraint.
    *
    * @example{{{
    *         x>0 |- [{x'=2&x>0}]x>=0     x>0 |- [{x'=2}]x>0
    *         -----------------------------------------------diffCut("x>0".asFormula)(1)
    *         x>0 |- [{x'=2}]x>=0
    * }}}
    * @example{{{
    *         x>0, x_0=x |- [{x'=2&x>=x_0}]x>=0     x>0, x_0=x |- [{x'=2}]x>=x_0
    *         -------------------------------------------------------------------diffCut("x>=old(x)".asFormula)(1)
    *         x>0 |- [{x'=2}]x>=0
    * }}}
    * @example{{{
    *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0&x>=x_0}]x>=0
    *                x>0, v>=0 |- [{x'=v,v'=1}]v>=0
    *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0}]x>=x_0
    *         --------------------------------------------------diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1)
    *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
    * }}}
    * @param formulas the list of formulas that will be cut into the differential equation in that order.
    *                 The formulas are typically shown to be differential invariants subsequently.
    *                 They can use old(x) and old(y) etc. to refer to the initial values of x and y, respectively.
    * @note diffCut is often needed when FV(post) depend on BV(ode) that are not in FV(constraint).
    * @see[[DC]]
    * @see [[diffInvariant()]]
    */
  //@todo("Remove the _* -- anti-pattern for stable tactics. Turn into a List or only allow a single invariant per call.", "4.2")
  def dC(formulas: Formula*)     : DependentPositionTactic = DifferentialTactics.diffCut(formulas:_*)

  /** Refine top-level antecedent/succedent ODE domain constraint
    * G|- [x'=f(x)&R]P, D     G|- [x'=f(x)&Q]R, (D)?
    * --- dR
    * G|- [x'=f(x)&Q]P, D
    * @param formula the formula R to refine Q to
    * @param hide whether to keep the extra succedents (D) around (default true), which makes position management easier
    */
  def dR(formula: Formula, hide: Boolean=true): DependentPositionTactic = DifferentialTactics.diffRefine(formula,hide)

  /** dI: Differential Invariant proves a formula to be an invariant of a differential equation (with the usual steps to prove it invariant)
    * (uses DI, DW, DE, QE)
    *
    * @param auto One of 'none, 'diffInd, 'full. Whether or not to automatically close and use DE, DW.
    *             'full: tries to close everything after diffInd rule
    *                    {{{
    *                        *
    *                      --------------------------
    *                      G |- [x'=f(x)&q(x)]p(x), D
    *                    }}}
    *             'none: behaves as DI rule per cheat sheet
    *                    {{{
    *                      G, q(x) |- p(x), D    G, q(x) |- [x'=f(x)&q(x)](p(x))', D
    *                      ---------------------------------------------------------
    *                                  G |- [x'=f(x)&q(x)]p(x), D
    *                    }}}
    *             'diffInd: behaves as diffInd rule per cheat sheet
    *                    {{{
    *                      G, q(x) |- p(x), D     q(x) |- [x':=f(x)]p(x')    @note derive on (p(x))' already done
    *                      ----------------------------------------------
    *                                  G |- [x'=f(x)&q(x)]p(x), D
    *                    }}}
    * @example{{{
    *         *
    *    ---------------------diffInd(qeTool, 'full)(1)
    *    x>=5 |- [{x'=2}]x>=5
    * }}}
    * @example{{{
    *    x>=5, true |- x>=5    true |- [{x':=2}]x'>=0
    *    --------------------------------------------diffInd(qeTool, 'diffInd)(1)
    *    x>=5 |- [{x'=2}]x>=5
    * }}}
    * @example{{{
    *    x>=5, true |- x>=5    x>=5, true |- [{x'=2}](x>=5)'
    *    ---------------------------------------------------diffInd(qeTool, 'none)(1)
    *    x>=5 |- [{x'=2}]x>=5
    * }}}
    * @example{{{
    *    x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
    *    -------------------------------------diffInd(qeTool, 'full)(1, 1::Nil)
    *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
    * }}}
    * @example
    * {{{
    * proveBy("x^2>=2->[{x'=x^3}]x^2>=2".asFormula, implyR(1) &
    *   diffInd()(1) & QE
    * )
    * }}}
    * @incontext
    */
  def dI(auto: Symbol = 'full): DependentPositionTactic = DifferentialTactics.diffInd(auto)
  /** DC+DI: Prove the given list of differential invariants in that order by DC+DI via [[dC]] followed by [[dI]]
    * Combines differential cut and differential induction. Use special function old(.) to introduce a ghost for the
    * starting value of a variable that can be used in the evolution domain constraint. Uses diffInd to prove that the
    * formulas are differential invariants. Fails if diffInd cannot prove invariants.
    *
    * @example{{{
    *         x>0 |- [{x'=2&x>0}]x>=0
    *         ------------------------diffInvariant("x>0".asFormula)(1)
    *         x>0 |- [{x'=2}]x>=0
    * }}}
    * @example{{{
    *         x>0, x_0=x |- [{x'=2&x>x_0}]x>=0
    *         ---------------------------------diffInvariant("x>old(x)".asFormula)(1)
    *                x>0 |- [{x'=2}]x>=0
    * }}}
    * @example{{{
    *         x>0, v>=0, x_0=x |- [{x'=v,v'=1 & v>=0&x>x_0}]x>=0
    *         ---------------------------------------------------diffInvariant("v>=0".asFormula, "x>old(x)".asFormula)(1)
    *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
    * }}}
    * @param invariants The differential invariants to cut in as evolution domain constraint.
    * @see [[dC]]
    * @see [[dI]]
    */
  //@todo("Remove the _* -- anti-pattern for stable tactics. Turn into a List or only allow a single invariant per call.", "4.2")
  def diffInvariant(invariants: Formula*): DependentPositionTactic = DifferentialTactics.diffInvariant(invariants:_*)
  /** DIo: Open Differential Invariant proves an open formula to be an invariant of a differential equation (with the usual steps to prove it invariant)
    * openDiffInd: proves an inequality to be an invariant of a differential equation (by DIo, DW, DE, QE)
    *           For strict inequalities, it uses open diff ind (<,>)
    *
    * @example{{{
    *         *
    *    ---------------------openDiffInd(1)
    *    x^2>5 |- [{x'=x^3+x^4}]x^2>5
    * }}}
    * @example{{{
    *         *
    *    ---------------------openDiffInd(1)
    *    x^3>5 |- [{x'=x^3+x^4}]x^3>5
    * }}}
    * @example
    * {{{
    * proveBy("x^2>9->[{x'=x^4}]x^2>9".asFormula, implyR(1) &
    *   openDiffInd()(1)
    * )
    * }}}
    */
  def openDiffInd: DependentPositionTactic = DifferentialTactics.openDiffInd

  /** DV: Differential Variant proves a formula to become true at some point after a differential equation.
    *
    * @example{{{
    *         *
    *    ------------------------- DV(1)
    *    a()>0 |- <{x'=a()}>x>=b()
    * }}}
    */
  def diffVar: DependentPositionTactic = DifferentialTactics.diffVar

  /** dG(ghost,r): Differential Ghost add auxiliary differential equations with extra variables
    * ghost of the form y'=a*y+b and the postcondition replaced by r, if provided.
    * {{{
    * G |- \exists y [x'=f(x),y'=g(x,y)&q(x)]r(x,y), D
    * ----------------------------------------------------------  dG using p(x) <-> \exists y. r(x,y) by QE
    * G |- [x'=f(x)&q(x)]p(x), D
    * }}}
    *
    * @note Uses QE to prove p(x) <-> \exists y. r(x,y)
    * @param ghost the extra differential equation for an extra variable y to ghost in of the form
    *              y'=a*y+b or y'=a*y or y'=b or y'=a*y-b
    * @param r the optional equivalent new postcondition to prove that can mention y; keeps p(x) if omitted.
    * @example
    * {{{
    * proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
    *   dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) &
    *     diffInd()(1, 0::Nil) & QE
    *   )
    * }}}
    * with optional instantiation of initial y
    * {{{
    * proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
    *   dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) &
    *     existsR("1/x^(1/2)".asFormula)(1) & diffInd()(1) & QE
    *   )
    * }}}
    */
  def dG(ghost: DifferentialProgram, r: Option[Formula]): DependentPositionTactic = DifferentialTactics.dG(ghost, r)


  // more

  /**
    * Generalize postcondition to C and, separately, prove that C implies postcondition.
    * The operational effect of {a;b;}@generalize(f1) is generalize(f1).
    * {{{
    *   genUseLbl:        genShowLbl:
    *   G |- [a]C, D      C |- B
    *   -------------------------
    *          G |- [a]B, D
    * }}}
    *
    * @example{{{
    *   genUseLbl:        genShowLbl:
    *   |- [x:=2;]x>1     x>1 |- [y:=x;]y>1
    *   ------------------------------------generalize("x>1".asFormula)(1)
    *   |- [x:=2;][y:=x;]y>1
    * }}}
    * @example{{{
    *   genUseLbl:                      genShowLbl:
    *   |- a=2 -> [z:=3;][x:=2;]x>1     x>1 |- [y:=x;]y>1
    *   -------------------------------------------------generalize("x>1".asFormula)(1, 1::1::Nil)
    *   |- a=2 -> [z:=3;][x:=2;][y:=x;]y>1
    * }}}
   */
  def generalize(C: Formula)  : DependentPositionTactic = DLBySubst.generalize(C)

  /** Prove the given cut formula to hold for the modality at position and turn postcondition into cut->post
    * The operational effect of {a;}*@invariant(f1,f2,f3) is postCut(f1) & postcut(f2) & postCut(f3).
    * {{{
    *   cutUseLbl:           cutShowLbl:
    *   G |- [a](C->B), D    G |- [a]C, D
    *   ---------------------------------
    *          G |- [a]B, D
    * }}}
    *
    * @example{{{
    *   cutUseLbl:                       cutShowLbl:
    *   |- [x:=2;](x>1 -> [y:=x;]y>1)    |- [x:=2;]x>1
    *   -----------------------------------------------postCut("x>1".asFormula)(1)
    *   |- [x:=2;][y:=x;]y>1
    * }}}
    * @example{{{
    *   cutUseLbl:                                     cutShowLbl:
    *   |- a=2 -> [z:=3;][x:=2;](x>1 -> [y:=x;]y>1)    |- [x:=2;]x>1
    *   -------------------------------------------------------------postCut("x>1".asFormula)(1, 1::1::Nil)
    *   |- a=2 -> [z:=3;][x:=2;][y:=x;]y>1
    * }}}
    */
  def postCut(cut: Formula)   : DependentPositionTactic = DLBySubst.postCut(cut)



  // closing

  /** QE: Quantifier Elimination to decide real arithmetic (after simplifying logical transformations).
    * Applies simplifying transformations to the real arithmetic questions before solving it via [[RCF]].
    * @param order the order of variables to use during quantifier elimination
    * @see [[QE]]
    * @see [[RCF]] */
  def QE(order: Seq[NamedSymbol] = Nil, requiresTool: Option[String] = None, timeout: Option[Int] = None): BelleExpr = {
    //@todo implement as part of tools?
    lazy val tool = ToolProvider.qeTool(requiresTool).getOrElse(
      throw new BelleThrowable(s"QE requires ${requiresTool.getOrElse("a QETool")}, but got None"))
    lazy val resetTimeout: (BelleExpr => BelleExpr) = timeout match {
      case Some(t) => tool match {
        case tom: ToolOperationManagement =>
          val oldTimeout = tom.getOperationTimeout
          tom.setOperationTimeout(t)
          if (oldTimeout != t) {
            (e: BelleExpr) => e > new DependentTactic("ANON") {
              override def computeExpr(v: BelleValue): BelleExpr = {
                tom.setOperationTimeout(oldTimeout)
                v match {
                  case _: BelleProvable => skip
                  case err: BelleValue with BelleThrowable => throw err
                }
              }
            }
          } else (e: BelleExpr) => e
        case _ => throw BelleUnsupportedFailure("Tool " + tool + " does not support timeouts")
      }
      case None => (e: BelleExpr) => e
    }
    lazy val timeoutTool: QETool = timeout match {
      case Some(t) => tool match {
        case tom: ToolOperationManagement =>
          tom.setOperationTimeout(t)
          tool
        case _ => throw BelleUnsupportedFailure("Tool " + tool + " does not support timeouts")
      }
      case None => tool
    }
    lazy val tactic = resetTimeout(ToolTactics.fullQE(order)(timeoutTool))
    (requiresTool, timeout) match {
      case (Some(toolName), Some(t)) => "QE" byWithInputs (Variable(toolName)::Number(t)::Nil, tactic)
      case (Some(toolName), None) => "QE" byWithInputs (Variable(toolName)::Nil, tactic)
      case (None, Some(t)) => "QE" byWithInputs (Number(t)::Nil, tactic)
      case _ => tactic
    }
  }
  def QE: BelleExpr = QE()

  /** Quantifier elimination returning equivalent result, irrespective of result being valid or not.
    * Performs QE and allows the goal to be reduced to something that isn't necessarily true.
    * @note You probably want to use fullQE most of the time, because partialQE will destroy the structure of the sequent
    */
  def partialQE: BelleExpr = ToolTactics.partialQE(ToolProvider.qeTool().getOrElse(throw new BelleThrowable("partialQE requires a QETool, but got None")))

  /** Splits propositional into many smallest possible QE calls.
    * @param split Configures how the tactic splits into smaller subgoals before QE (default: exhaustive alpha and beta rules).
    * @param preQE Tactic to execute before each individual QE call (default: skip).
    * @param qe How to QE
    */
  def atomicQE(split: BelleExpr = SaturateTactic(onAll(alphaRule | betaRule)), preQE: BelleExpr = skip, qe: BelleExpr = QE): BelleExpr =
    split & onAll(preQE & qe & done)
  def atomicQE: BelleExpr = atomicQE()

  def heuQE: BelleExpr = ToolTactics.heuristicQE(ToolProvider.qeTool().getOrElse(throw new BelleThrowable("QE requires a QETool, but got None")))
  def heuQEPO (po:Ordering[Variable]): BelleExpr = ToolTactics.heuristicQE(ToolProvider.qeTool().getOrElse(throw new BelleThrowable("QE requires a QETool, but got None")),po)
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Bigger Tactics.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Utility Tactics
  /** nil=skip is a no-op tactic that has no effect */
  val nil : BelleExpr = Idioms.ident
  /** nil=skip is a no-op tactic that has no effect
    * @see [[done]] */
  val skip : BelleExpr = nil
  /** fail is a tactic that always fails
    * @see [[skip]] */
  val fail : BelleExpr = assertT(seq=>false, "fail")
  /** done: check that the current goal is proved and fail if it isn't.
    * @see [[skip]] */
  val done : BelleExpr = DebuggingTactics.done


  /** abbrv(name) Abbreviate the term at the given position by a new name and use that name at all occurrences of that term.
    * @example{{{
    *   maxcd = max(c,d) |- a+b <= maxcd+e
    *   ----------------------------------------abbrv(Variable("maxcd"))(1, 1::0::Nil)
    *                    |- a+b <= max(c, d) + e
    * }}}
    * @param name The new variable to use as an abbreviation.
    * */
  def abbrv(name: Variable): DependentPositionTactic = EqualityTactics.abbrv(name)
  /** Rewrites free occurrences of the left-hand side of an equality into the right-hand side at a specific position.
    * @example{{{
    *    x=0 |- 0*y=0, x+1>0
    *    ---------------------eqL2R(-1)(1)
    *    x=0 |- x*y=0, x+1>0
    * }}}
    * @param eqPos The position of the equality. If it points to a formula, it rewrites all occurrences of left in that formula.
    *              If it points to a specific term, then only this term is rewritten.
    */
  //@todo missing AxiomInfo for tactic extraction
  def eqL2R(eqPos: Int): DependentPositionTactic = EqualityTactics.eqL2R(eqPos)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = EqualityTactics.eqL2R(eqPos)
  /** Rewrites free occurrences of the right-hand side of an equality into the left-hand side at a specific position ([[EqualityTactics.eqR2L]]). */
  def eqR2L(eqPos: Int): DependentPositionTactic = EqualityTactics.eqR2L(eqPos)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = EqualityTactics.eqR2L(eqPos)
  /** Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively ([[EqualityTactics.exhaustiveEqL2R]]). */
  lazy val exhaustiveEqL2R: DependentPositionTactic = exhaustiveEqL2R(false)
  def exhaustiveEqL2R(hide: Boolean = false): DependentPositionTactic =
    if (hide) "allL2R" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(fml@Equal(_, _)) => EqualityTactics.exhaustiveEqL2R(pos) & hideL(pos, fml)
    })
    else EqualityTactics.exhaustiveEqL2R
  /** Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively ([[EqualityTactics.exhaustiveEqR2L]]). */
  lazy val exhaustiveEqR2L: DependentPositionTactic = exhaustiveEqR2L(false)
  def exhaustiveEqR2L(hide: Boolean = false): DependentPositionTactic =
    if (hide) "allR2L" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(fml@Equal(_, _)) => EqualityTactics.exhaustiveEqR2L(pos) & hideL(pos, fml)
    })
    else EqualityTactics.exhaustiveEqR2L

  /** Transform an FOL formula or term into the formula/term 'to'.
    * A proof why that tranformation is acceptable will be shown on demand.
    * Transforms the FOL formula or term at position 'pos' into the formula/term 'to'. Uses QE to prove the transformation correct.
    * @example {{{
    *                           *
    *                           --------------
    *           a<b |- a<b      |- a<b -> b>a
    *           ------------------------------ transform("a<b".asFormula)(1)
    *           a<b |- b>a
    * }}}
    * @example {{{
    *                                         *
    *                                    ---------------------
    *           a+b<c, b>=0 |- a+b<c     b>=0 |- a+b<c -> a<c
    *           ---------------------------------------------- transform("a+b<c".asFormula)(1)
    *           a+b<c, b>=0 |- a<c
    * }}}
    * @example {{{
    *                           *
    *                           ---------------
    *           a<c |- a<c      |- c+0=c
    *           -------------------------------transform("c".asFormula)(1, 1::Nil)
    *           a<c |- a<c+0
    * }}}
    * @param to The transformed formula or term that is desired as the result of this transformation.
    */
  def transform(to: Expression): DependentPositionTactic = ToolTactics.transform(to)

  /** Determines difference between expression at position and expression `to` and turns diff.
    * into transformations and abbreviations. */
  def edit(to: Expression): DependentPositionTactic = ToolTactics.edit(to)

  //
  /** OnAll(e) == <(e, ..., e) runs tactic `e` on all current branches. */
  def onAll(e: BelleExpr): BelleExpr = OnAll(e)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Contract Tactics and Debugging Tactics
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Tactic contracts
  /** Assert that the given condition holds for the goal's sequent. */
  def assertT(cond : Sequent=>Boolean, msg: => String): BelleExpr = DebuggingTactics.assert(cond, msg)
  /** Assert that the sequent has the specified number of antecedent and succedent formulas, respectively. */
  def assertT(antecedents: Int, succedents: Int, msg: => String = ""): BelleExpr = DebuggingTactics.assert(antecedents, succedents, msg)

  // PositionTactic contracts
  /** Assert that the given condition holds for the sequent at the position where the tactic is applied */
  def assertT(cond : (Sequent,Position)=>Boolean, msg: => String): BuiltInPositionTactic = DebuggingTactics.assert(cond, msg)
  /** Assert that the given expression is present at the position in the sequent where this tactic is applied to. */
  def assertE(expected: => Expression, msg: => String): BuiltInPositionTactic = DebuggingTactics.assertE(expected, msg)

  /** errorT raises an error upon executing this tactic, stopping processing */
  def errorT(msg: => String): BuiltInTactic = DebuggingTactics.error(msg)

  /** debug(s) sprinkles debug message s into the output and the ProofNode information */
  def debug(s: => Any): BuiltInTactic = DebuggingTactics.debug(s.toString)
  /** debugAt(s) sprinkles debug message s into the output and the ProofNode information */
  def debugAt(s: => Any): BuiltInPositionTactic = DebuggingTactics.debugAt(s.toString)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Special functions
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /** Expands absolute value using `abs(x)=y <-> (x>=0&y=x | x<=0&y=-x)`, see [[EqualityTactics.abs]] */
  lazy val abs: DependentPositionTactic = EqualityTactics.abs
  /** Expands minimum function using `min(x,y)=z <-> (x<=y&z=x | x>=y&z=y)`, see [[EqualityTactics.minmax]] */
  lazy val min: DependentPositionTactic = EqualityTactics.minmax
  /** Expands maximum function using `max(x,y)=z <-> (x>=y&z=x | x<=y&z=y)`, see [[EqualityTactics.minmax]] */
  lazy val max: DependentPositionTactic = EqualityTactics.minmax

  /** Alpha rules are propositional rules that do not split */
  lazy val alphaRule: BelleExpr = andL('_) |
    (orR('_) |
      (implyR('_) |
        (notL('_) |
          notR('_)
          )
        )
      )

  /** Beta rules are propositional rules that split */
  lazy val betaRule: BelleExpr = andR('_) |
    (orL('_) |
      (implyL('_) |
        (equivL('_) |
          equivR('_)
          )
        )
      )

  /** Real-closed field arithmetic on a single formula without any extra smarts and simplifications.
    * @see [[QE]] */
  def RCF: BelleExpr = ToolTactics.rcf(ToolProvider.qeTool().getOrElse(throw new BelleThrowable("RCF requires a QETool, but got None")))

//  /** Lazy Quantifier Elimination after decomposing the logic in smart ways */
//  //@todo ideally this should be ?RCF so only do anything of RCF if it all succeeds with true
//  def lazyQE = (
//    ((alphaRule | allR('_) | existsL('_)
//          | close
//          //@todo eqLeft|eqRight for equality rewriting directionally toward easy
//          //| (la(TacticLibrary.eqThenHideIfChanged)*)
//          | betaRule)*)
//      | QE)



  // Global Utility Functions

  /**
    * The position of `here()` in the formula `fml`.
    * @return The term or formula position where `here()` occurs in `fml`.
    * @throws IllegalArgumentException if `here()` does not occur in `fml`.
    * @example {{{
    *    positionOf("p() & x>2 -> here() | x=y^2".asFormula) == PosInExpr(1::0::Nil)
    *    positionOf("p() & here() -> x=1 | x=y^2".asFormula) == PosInExpr(0::1::Nil)
    *    positionOf("p() & x>2 -> x=1 | here()=y^2".asFormula) == PosInExpr(1::1::0::Nil)
    *    positionOf("p() & x>2 -> x=1 | x=here()^2".asFormula) == PosInExpr(1::1::1::0::Nil)
    *    positionOf("_ & here() -> _ | _".asFormula) == PosInExpr(0::1::Nil)
    *    positionOf("_ & _ -> _ | .=here()^2".asFormula) == PosInExpr(1::1::1::0::Nil)
    *    positionOf("_ & here() -> _".asFormula) == PosInExpr(0::1::Nil)
    * }}}
    */
  def positionOf(fml: Formula): PosInExpr = fml.find(e =>
    e==FuncOf(Function("here",None,Unit,Real),Nothing) || e==PredOf(Function("here",None,Unit,Bool),Nothing)
  ) match {
    case Some((pos,_)) => pos
    case None => throw new IllegalArgumentException("here() locator does not occur in positionOf(" + fml + ")")
  }

  /** ifThenElse(cond,thenT,elseT) runs `thenT` if `cond` holds at position and `elseT` otherwise. */
  def ifThenElse(cond: (Sequent, Position)=>Boolean, thenT: BelleExpr, elseT: BelleExpr): DependentPositionTactic = "ifThenElse" by ((pos:Position,seq:Sequent) =>
    if (cond(seq, pos))
      thenT
    else
      elseT
    )

  /**
    * Prove the new goal by the given tactic, returning the resulting Provable
    *
    * @see [[SequentialInterpreter]]
    * @see [[TactixLibrary.by(Provable)]]
    * @see [[proveBy()]]
    */
  def proveBy(goal: ProvableSig, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(goal)
    BelleInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
//      //@note there is no other case at the moment
//      case r => throw BelleIllFormedError("Error in proveBy, goal\n" + goal + " was not provable but instead resulted in\n" + r)
    }
  }

  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
    *
   * @see [[SequentialInterpreter]]
   * @see [[TactixLibrary.by(Provable)]]
   * @see [[proveBy()]]
   * @example {{{
   *   import StringConverter._
   *   import TactixLibrary._
   *   val proof = TactixLibrary.proveBy(Sequent(IndexedSeq(), IndexedSeq("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula)), prop)
   * }}}
   */
  def proveBy(goal: Sequent, tactic: BelleExpr): ProvableSig = proveBy(ProvableSig.startProof(goal), tactic)
  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
    *
   * @see [[TactixLibrary.by(Provable)]]
   * @example {{{
   *   import StringConverter._
   *   import TactixLibrary._
   *   val proof = TactixLibrary.proveBy("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula, prop)
   * }}}
   */
  def proveBy(goal: Formula, tactic: BelleExpr): ProvableSig = proveBy(Sequent(IndexedSeq(), IndexedSeq(goal)), tactic)

  /** useLemma(lemmaName, tactic) applies the lemma identified by `lemmaName`, optionally adapting the lemma formula to
    * the current subgoal using the tactic `adapt`. Literal lemma application if `adapt` is None. */
  def useLemma(lemmaName: String, adapt: Option[BelleExpr]): BelleExpr = "useLemma" byWithInputs(
    if (adapt.isDefined) lemmaName::adapt.get.prettyString::Nil else lemmaName::Nil,
    anon { _ =>
      val userLemmaName = "user" + File.separator + lemmaName //@todo FileLemmaDB + multi-user environment
      if (LemmaDBFactory.lemmaDB.contains(userLemmaName)) {
        val lemma = LemmaDBFactory.lemmaDB.get(userLemmaName).get
        adapt match {
          case Some(t) => cut(lemma.fact.conclusion.succ.head) <(t, cohideR('Rlast) & by(lemma))
          case None => by(lemma)
        }
      } else throw new BelleAbort("Missing lemma " + lemmaName, "Please prove lemma " + lemmaName + " first")
    }
  )

  /** Applies the lemma by matching `key` in the lemma with the tactic position. */
  def useLemmaAt(lemmaName: String, key: Option[PosInExpr]): DependentPositionWithAppliedInputTactic = "useLemmaAt" byWithInputs(
    if (key.isDefined) lemmaName::key.get.prettyString.substring(1)::Nil else lemmaName::Nil, //@note remove leading . from PosInExpr
    (pos: Position, _: Sequent) => {
      val userLemmaName = "user" + File.separator + lemmaName //@todo FileLemmaDB + multi-user environment
      if (LemmaDBFactory.lemmaDB.contains(userLemmaName)) {
        val lemma = LemmaDBFactory.lemmaDB.get(userLemmaName).get
        useAt(lemma, key.getOrElse(PosInExpr(0::Nil)))(pos)
      } else throw new BelleAbort("Missing lemma " + lemmaName, "Please prove lemma " + lemmaName + " first")
    })

  /** Finds a counter example, indicating that the specified formula is not valid. */
  def findCounterExample(formula: Formula) = ToolProvider.cexTool().getOrElse(throw new BelleThrowable("findCounterExample requires a CounterExampleTool, but got None")).findCounterExample(formula)


  ///

  /* Axiom and tactic index for stepAt */
  private def sequentStepIndex(isAnte: Boolean)(expr: Expression): Option[String] = (expr, isAnte) match {
    case (True, false) => Some("closeTrue")
    case (False, true) => Some("closeFalse")
    // prefer simplification over left-right-swaps
    case (Not(Box(_,Not(_))), _) => Some("<> diamond")
    case (Not(Diamond(_,Not(_))), _) => Some("[] box")
    case (_: Not, true) => Some("notL")
    case (_: Not, false) => Some("notR")
    case (_: And, true) => Some("andL")
    case (_: And, false) => Some("andR")
    case (_: Or, true) => Some("orL")
    case (_: Or, false) => Some("orR")
    case (_: Imply, true) => Some("implyL")
    case (_: Imply, false) => Some("implyR")
    case (_: Equiv, true) => Some("equivL")
    case (_: Equiv, false) => Some("equivR")
    case (_: Forall, true) => Some("allL")
    case (_: Forall, false) => Some("allR")
    case (_: Exists, true) => Some("existsL")
    case (_: Exists, false) => Some("existsR")
    case _ => AxiomIndex.axiomFor(expr) /* @note same as HilbertCalculus.stepAt(pos) */
  }


}
