/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.{Augmentors, DerivationInfo, FormulaTools}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{Location, UnknownLocation}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

object BelleExpr {
  private[keymaerax] val DEBUG = System.getProperty("DEBUG", "false")=="true"
  private[keymaerax] val RECHECK = System.getProperty("DEBUG", "false")=="true"
}

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron tactic expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 *
 * @todo Consolidate the members of BelleExpr and finalize an abstract syntax.
 * @author Nathan Fulton
 * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.SequentialInterpreter]]
 * @see [[edu.cmu.cs.ls.keymaerax.bellerophon]]
 */
abstract class BelleExpr(private var location: Location = UnknownLocation) {
  private[keymaerax] val DEBUG = BelleExpr.DEBUG
  // tactic combinators

  /** this & other: sequential composition executes other on the output of this, failing if either fail. */
  def &(other: BelleExpr)             = SeqTactic(this, other)
  /** this | other: alternative composition executes other if applying this fails, failing if both fail. */
  def |(other: BelleExpr)             = EitherTactic(this, other)
  /** (this*): saturating repetition executes this tactic to a fixpoint, casting result to type annotation, diverging if no fixpoint. */
  def * = SaturateTactic(this)
  /** this+: saturating repetition executes this tactic to a fixpoint, requires at least one successful application */
  //def + = this & this.*
  /** this*n: bounded repetition executes this tactic to `times` number of times, failing if any of those repetitions fail. */
  def *(n: Int) = RepeatTactic(this, n)
  /** <(e1,...,en): branching to run tactic `ei` on branch `i`, failing if any of them fail or if there are not exactly `n` branches.
    * @note Equivalent to {{{a & Idioms.<(b,c)}}} */
  //@deprecated("Use & with explicit Idioms.< instead; import Idioms.<, so a & <(b,c)", since="4.2")
  def <(children: BelleExpr*)         = SeqTactic(this, BranchTactic(children))
  /** case _ of {fi => ei} uniform substitution case pattern applies the first ei such that fi uniformly substitutes to current provable for which ei does not fail, fails if the ei of all matching fi fail. */
  def U(p: (SequentType, RenUSubst => BelleExpr)*) = SeqTactic(this, USubstPatternTactic(p))
  /** partial: marks a tactic that is allowed to not close all its goals. */
  def partial(label: BelleLabel)      = PartialTactic(this, Some(label))
  /** partial: marks a tactic that is allowed to not close all its goals. */
  def partial                         = PartialTactic(this)
  //@todo Maybe support ?(e) or try(e) or optional(e) defined as this|skip

  override def toString: String = prettyString
  /** pretty-printed form of this Bellerophon tactic expression */
  def prettyString: String

  /** @note location is private so that it's not something that effects case class quality, and mutable so that it can be ignored when building up custom tactics. */
  def setLocation(newLocation: Location) = location = newLocation
  def getLocation = location
}

/** A BelleExpr that has a proper code name, so is not just used internally during application. */
trait NamedBelleExpr extends BelleExpr {
  /** The code name of this Belle Expression */
  val name: String

  override def prettyString: String = name
}

/** Give a code name to the given tactic `tactic` for serialization purposes. */
case class NamedTactic(name: String, tactic: BelleExpr) extends NamedBelleExpr {
  //@todo make this an assert.
  if(name != "ANON" && !DerivationInfo.hasCodeName(name)) println(s"WARNING: NamedTactic was named ${name} but this name does not appear in DerivationInfo's list of codeNames.")
}

/* Common base class for built-in tactics coming from the base layer of the tactic library directly manipulate core Provables. */
abstract case class BuiltInTactic(name: String) extends NamedBelleExpr {
  private[bellerophon] final def execute(provable: ProvableSig): ProvableSig = try {
    result(provable)
  } catch {
    case be: BelleThrowable => throw be
    case e: MatchError => throw new BelleTacticFailure(s"Formula did not have the shape expected by ${name}: " + e.getMessage, e)
  }
  private[bellerophon] def result(provable : ProvableSig): ProvableSig
}
case class LabelBranch(label: BelleLabel) extends BelleExpr { override def prettyString: String = s"Label ${label.prettyString}" }

/** ⎵: Placeholder for tactics in tactic contexts. Reserved tactic expression */
class BelleDot() extends BelleExpr { override def prettyString = ">>_<<" }
object BelleDot extends BelleDot()

////////////////////////////////////////////////////////////////////////////////////////////////////
// Positional tactics
////////////////////////////////////////////////////////////////////////////////////////////////////

/** Applied at a position, AtPosition turns into a tactic of type T. Turns a position or position locator into a tactic.
  * That is, an AtPosition[T] tactic is essentially a function of type
  * {{{
  *   Position => T
  * }}}
  * but one that also supports indirect positioning via position locators that merely identify positions
  * {{{
  *   PositionLocator => T
  * }}}
  *
  * An AtPosition tactic `t` supports [[Position direct positions]] and indirect [[PositionLocator position locators]].
  *
  *   - `t(1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula.
  *   - `t(-1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula.
  *   - `t(-4, 0::1::1::Nil)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fourth antecedent formula,
  *     that is at the second child of the second child of the first child of the fourth antecedent formula in the sequent.
  *   - `t('L)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] (left side of the sequent).
  *   - `t('R)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] (right side of the sequent).
  *   - `t('_)` applied at the first applicable position in the side of the sequent to which tactic `t` applies.
  *     The side of the sequent is uniquely determined by type of tactic.
  *   - `t('Llast)` applied at the last antecedent position (left side of the sequent).
  *   - `t('Rlast)` applied at the last succedent position (right side of the sequent).
  *
  * In addition, the formulas expected or sought for at the respective positions identified by the locators can be provided,
  * which is useful for tactic contract and tactic documentation purposes.
  * It is also useful for finding a corresponding formula by pattern matching.
  *
  *   - `t(2, fml)` applied at the second [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula,
  *     ensuring that the formula `fml` is at that position.
  *   - `t(-2, fml)` applied at the second [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula,
  *     ensuring that the formula `fml` is at that position.
  *   - `t(5, 0::1::1::Nil, ex)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fifth succedent formula,
  *     that is at the second child of the second child of the first child of the fifth succcedent formula in the sequent,
  *     ensuring that the expression `ex` is at that position.
  *   - `t('L, fml)` applied at the antecedent position (left side of the sequent)
  *     where the expected formula `fml` can be found (on the top level).
  *   - `t('R, fml)` applied at the succedent position (right side of the sequent)
  *     where the expected formula `fml` can be found (on the top level).
  *   - `t('_, fml)` applied at the suitable position (uniquely determined by type of tactic)
  *     where the expected formula `fml` can be found (on the top level).
  *
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
trait AtPosition[T <: BelleExpr] extends BelleExpr with (PositionLocator => T) {
  import Find._

  /**
    * Returns the tactic that can be applied at the position identified by `locator`.
    *
    * @param locator The locator: Fixed, Find, LastAnte, or LastSucc
    * @return The tactic of type `T` that can be readily applied at the position identified by `locator` to any given BelleExpr.
    * @see [[PositionLocator]]
    */
  def apply(locator: PositionLocator): T

  /**
   * Applied at a fixed position.
   * @param position The position where this tactic will be applied at.
   * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note Convenience wrapper
   * @see [[apply(locator: PositionLocator)]]
   * @see [[Fixed]]
   */
  /*private[keymaerax]*/ final def apply(position: Position): T = apply(Fixed(position))
  /**
    * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
    *
    * @param position The position where this tactic will be applied at.
    * @param expected the formula expected at `position`. Contract fails if that expectation is not met.
    * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
    * @note Convenience wrapper
    * @see [[apply(locator: PositionLocator)]]
    * @see [[Fixed]]
    */
  /*private[keymaerax]*/ final def apply(position: Position, expected: Formula): T = apply(Fixed(position, Some(expected)))
  /**
    * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
    *
    * @param seqIdx The position where this tactic will be applied at (-1 based for antecedent, 1 based for succedent).
    * @param expected the formula expected at `position`. Contract fails if that expectation is not met.
    * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
    * @note Convenience wrapper
    * @see [[apply(locator: PositionLocator)]]
    * @see [[Fixed]]
    */
  final def apply(seqIdx: Int, expected: Formula): T = apply(Fixed(Position(seqIdx), Some(expected)))
  /**
    * Applied at a fixed position, ensuring that the formula `expected` will be found at that position, verbatim.
    *
    * @param seqIdx The position where this tactic will be applied at (-1 based for antecedent, 1 based for succedent).
    * @param expected the formula expected at `position`. Contract fails if that expectation is not met.
    * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
    * @note Convenience wrapper
    * @see [[apply(locator: PositionLocator)]]
    * @see [[Fixed]]
    */
  final def apply(seqIdx: Int, inExpr: List[Int], expected: Formula): T = apply(Fixed(Position(seqIdx, inExpr), Some(expected)))
  final def apply(seqIdx: Int, inExpr: PosInExpr, expected: Formula): T = apply(seqIdx, inExpr.pos, expected)
  private[ls] final def apply(position: SeqPos): T = apply(Fixed(Position(position)))

  /**
   * Applied at a fixed position in (signed) sequent position `seqIdx` at subexpression `inExpr`.
    *
    * @param seqIdx The signed index in the sequent (strictly negative index for antecedent, strictly positive for succedent).
   * @param inExpr Where to apply inside the formula at index seqIdx interpreted as a [[PosInExpr]].
   * @return The tactic of type `T` that can be readily applied at the specified position to any given BelleExpr.
   * @note Convenience wrapper
   * @see [[PosInExpr]]
   * @see [[apply(position: Position)]]
   * @see [[Fixed]]
   */
  final def apply(seqIdx: Int, inExpr: List[Int] = Nil): T = apply(Fixed(Position(seqIdx, inExpr)))
  final def apply(seqIdx: Int, inExpr: PosInExpr): T = apply(Fixed(Position(seqIdx, inExpr.pos)))
  /**
    * Returns the tactic at the position identified by `locator`.
    *
    * @param locator The locator symbol at which to apply this AtPosition:
    *                'L (find left),
    *                'R (find right),
    *                '_ (find left/right appropriately for tactic),
    *                'Llast (at last position in antecedent), or
    *                'Rlast (at last position in succedent).
    * @note Convenience wrapper
    * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.AtPosition]]
    * @see [[apply(locator: PositionLocator)]]
    */
  //@todo turn into properly type-checkable locator arguments without going crazy long.
  final def apply(locator: Symbol): T = locator match {
    case 'L => apply(FindL(0, None))
    case 'R => apply(FindR(0, None))
    case '_ => this match {
      case _: BuiltInLeftTactic => apply(FindL(0, None))
      case _: BuiltInRightTactic => apply(FindR(0, None))
      case _ => throw new BelleThrowable(s"Cannot determine whether this tactic is left/right. Please use 'L or 'R as appropriate.")
    }
    case 'Llast => apply(LastAnte(0))
    case 'Rlast => apply(LastSucc(0))
  }
  /**
    * Returns the tactic at the position identified by `locator`, ensuring that `locator` will yield the formula `expected` verbatim.
    *
    * @param locator The locator symbol at which to apply this AtPosition:
    *                'L (find left),
    *                'R (find right),
    *                '_ (find left/right appropriately for tactic),
    *                'Llast (at last position in antecedent), or
    *                'Rlast (at last position in succedent).
    * @param expected the formula expected at the position that `locator` identifies. Contract fails if that expectation is not met.
    * @note Convenience wrapper
    * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.AtPosition]]
    * @see [[apply()]]
    */
  final def apply(locator: Symbol, expected: Expression): T = locator match {
    case 'L => apply(FindL(0, Some(expected)))
    case 'Llike => apply(FindL(0, Some(expected), exact=false))
    case 'R => apply(FindR(0, Some(expected)))
    case 'Rlike => apply(FindR(0, Some(expected), exact=false))
    case '_ => this match {
      case _: BuiltInLeftTactic => apply(FindL(0, Some(expected)))
      case _: BuiltInRightTactic => apply(FindR(0, Some(expected)))
      case _ => throw new BelleThrowable(s"Cannot determine whether this tactic is left/right. Please use 'L or 'R as appropriate.")
    }
    //@todo how to check expected formula?
    case 'Llast => println("INFO: will not check expected for 'Llast yet"); apply(LastAnte(0))
    case 'Rlast => println("INFO: will not check expected for 'Rlast yet"); apply(LastSucc(0))
  }

}

/** PositionTactics are tactics that can be [[AtPosition applied at positions]] giving ordinary tactics.
  *
  * @see [[AtPosition]] */
trait PositionalTactic extends BelleExpr with AtPosition[AppliedPositionTactic] {
  /** @note this should be called from within interpreters, but not by end-users */
  def computeResult(provable: ProvableSig, position: Position): ProvableSig
  final override def apply(locator: PositionLocator): AppliedPositionTactic = AppliedPositionTactic(this, locator)
}

/** Built-in position tactics such as assertAt */
abstract case class BuiltInPositionTactic(name: String) extends PositionalTactic with NamedBelleExpr

/** Built-in position tactics that are to be applied on the left */
abstract case class BuiltInLeftTactic(name: String) extends PositionalTactic with NamedBelleExpr {
  final override def computeResult(provable: ProvableSig, position:Position): ProvableSig = position match {
    case p: AntePosition => computeAnteResult(provable, p)
    case _ => throw BelleIllFormedError("LeftTactics can only be applied at a left position not at " + position)
  }

  def computeAnteResult(provable: ProvableSig, pos: AntePosition): ProvableSig
}

/** Built-in position tactics that are to be applied on the right */
abstract case class BuiltInRightTactic(name: String) extends PositionalTactic with NamedBelleExpr {
  final override def computeResult(provable: ProvableSig, position:Position): ProvableSig = position match {
    case p: SuccPosition => computeSuccResult(provable, p)
    case _ => throw BelleIllFormedError("RightTactics can only be applied at a right position not at " + position)
  }

  def computeSuccResult(provable: ProvableSig, pos: SuccPosition) : ProvableSig
}

@deprecated
abstract case class DependentTwoPositionTactic(name: String) extends NamedBelleExpr {
  override def prettyString: String = s"UnappliedTwoPositionTactic of name ${name}" //@todo

  def computeExpr(p1: Position, p2: Position): DependentTactic

  def apply(p1: Position, p2: Position) = AppliedDependentTwoPositionTactic(this, p1, p2)
}
@deprecated
case class AppliedDependentTwoPositionTactic(t: DependentTwoPositionTactic, p1: Position, p2: Position) extends BelleExpr {
  /** pretty-printed form of this Bellerophon tactic expression */
  override def prettyString: String = t.prettyString + "(" + p1 + "," + p2 + ")"
}

/**
  * Stores the position tactic and position at which the tactic was applied.
  * Useful for storing execution traces.
  */
case class AppliedPositionTactic(positionTactic: PositionalTactic, locator: PositionLocator) extends BelleExpr {
  import Augmentors._
  final def computeResult(provable: ProvableSig) : ProvableSig = try { locator match {
      //@note interprets PositionLocator
      case Fixed(pos, shape, exact) => shape match {
        case Some(f:Formula) =>
          require(provable.subgoals.size == 1, "Locator 'fixed with shape' applies only to provables with exactly 1 subgoal since otherwise ill-defined")
          //@note (implicit .apply needed to ensure subposition to pos.inExpr
          if (( exact && provable.subgoals.head.sub(pos).contains(f)) ||
              (!exact && UnificationMatch.unifiable(f, provable.subgoals.head.sub(pos).get).isDefined)) {
            positionTactic.computeResult(provable, pos)
          } else {
            throw new BelleIllFormedError("Formula " + provable.subgoals.head.sub(pos) + " at position " + pos +
              " is not of expected shape " + f)
          }
        case None => positionTactic.computeResult(provable, pos)
      }
      case Find(goal, shape, start, exact) =>
        require(start.isTopLevel, "Start position must be top-level in sequent")
        require(start.isIndexDefined(provable.subgoals(goal)), "Start position must be valid in sequent")
        tryAllAfter(provable, goal, shape, start, exact, null)
      case LastAnte(goal) => positionTactic.computeResult(provable, AntePosition.base0(provable.subgoals(goal).ante.size-1))
      case LastSucc(goal) => positionTactic.computeResult(provable, SuccPosition.base0(provable.subgoals(goal).succ.size-1))
    }
  } catch {
    case be: BelleThrowable => throw be
    //note the following exceptions are likely caused by wrong positioning
    case ex: IndexOutOfBoundsException => throw new BelleThrowable("Position " + locator +
      " may point outside the positions of the goal " + provable.prettyString, ex)
    case ex: MatchError => throw new BelleThrowable("Tactic " + positionTactic.prettyString +
      " applied at " + locator + " on a non-matching expression in " + provable.prettyString, ex)
    //@note wrap failing assertions etc. so that searchy tactic combinators follow up on the tactic failure
    case t: Throwable => throw new BelleThrowable(t.getMessage, t)
  }

  /** Recursively tries the position tactic at positions at or after pos in the specified provable. */
  private def tryAllAfter(provable: ProvableSig, goal: Int, shape: Option[Expression], pos: Position, exact: Boolean,
                          cause: BelleThrowable): ProvableSig =
    if (pos.isIndexDefined(provable.subgoals(goal))) {
      try {
        shape match {
          case Some(f: Formula) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isDefined =>
            positionTactic.computeResult(provable, pos)
          case Some(f: Formula) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isEmpty =>
            tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, new BelleThrowable(s"Formula is not of expected shape", cause))
          case Some(f: Formula) if exact && provable.subgoals(goal)(pos.top) == f => positionTactic.computeResult(provable, pos)
          case Some(f: Formula) if exact && provable.subgoals(goal)(pos.top) != f =>
            tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, new BelleThrowable(s"Formula is not of expected shape", cause))
          case Some(t: Term) =>
            val tPos = FormulaTools.posOf(provable.subgoals(goal)(pos.top), e => if (exact) e == t else UnificationMatch.unifiable(e, t).isDefined)
            if (tPos.isEmpty) tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, new BelleThrowable(s"Formula is not of expected shape", cause))
            else positionTactic.computeResult(provable, pos.topLevel ++ tPos.head)
          case None => positionTactic.computeResult(provable, pos)
        }
      } catch {
        //@todo should catch only fails not eat problems
        case e: Throwable =>
          val newCause = if (cause == null) new BelleThrowable(s"Position tactic ${positionTactic.prettyString} is not " +
            s"applicable at ${pos.prettyString}", e)
          else new CompoundException(
            new BelleThrowable(s"Position tactic ${positionTactic.prettyString} is not applicable at ${pos.prettyString}", e),
            cause)
          tryAllAfter(provable, goal, shape, pos.advanceIndex(1), exact, newCause)
      }
    } else throw cause

  override def prettyString = positionTactic.prettyString + "(" + locator.prettyString + ")"
}

abstract case class BuiltInTwoPositionTactic(name: String) extends NamedBelleExpr {
  /** @note this should be called from within interpreters, but not by end users. */
  def computeResult(provable : ProvableSig, posOne: Position, posTwo: Position) : ProvableSig

  /** Returns an explicit representation of the application of this tactic to the provided positions. */
  final def apply(posOne: Position, posTwo: Position): AppliedBuiltinTwoPositionTactic = AppliedBuiltinTwoPositionTactic(this, posOne, posTwo)
  /** Returns an explicit representation of the application of this tactic to the provided positions.
    *
    * @note Convenience wrapper
    */
  final def apply(posOne: Int, posTwo: Int): AppliedBuiltinTwoPositionTactic = apply(Position(posOne), Position(posTwo))
}

/** Motivation is similar to [[AppliedPositionTactic]], but for [[BuiltInTwoPositionTactic]] */
case class AppliedBuiltinTwoPositionTactic(positionTactic: BuiltInTwoPositionTactic, posOne: Position, posTwo: Position) extends BelleExpr {
  final def computeResult(provable: ProvableSig) : ProvableSig = try {
    positionTactic.computeResult(provable, posOne, posTwo)
  } catch {
    case be: BelleThrowable => throw be
    case t: Throwable => throw new BelleThrowable(t.getMessage, t)
  }

  override def prettyString = positionTactic.prettyString + "(" + posOne.prettyString + "," + posTwo.prettyString + ")"
}

/**
 * Dependent tactics compute a tactic to apply based on their input.
 * These tactics are probably not necessary very often, but are useful for idiomatic shortcuts.
 * See e.g., AtSubgoal.
  *
  * @note similar to the ConstructionTactics in the old framework, except they should not be necessary
 *       nearly as often because BuiltIns have direct access to a Provable.
 * @param name The name of the tactic.
 * @todo is there a short lambda abstraction notation as syntactic sugar?
 */
abstract case class DependentTactic(name: String) extends NamedBelleExpr {
  def computeExpr(provable: ProvableSig): BelleExpr = throw new BelleThrowable("Not implemented")
  def computeExpr(e: BelleValue with BelleThrowable): BelleExpr = throw e
  /** Generic computeExpr; prefer overriding computeExpr(Provable) and computeExpr(BelleThrowable) */
  def computeExpr(v : BelleValue): BelleExpr = try { v match {
      case BelleProvable(provable, _) => computeExpr(provable)
      case e: BelleThrowable => computeExpr(e)
    }
  } catch {
    case be: BelleThrowable => throw be
    case t: Throwable => if (DEBUG) t.printStackTrace(); throw new BelleThrowable(t.getMessage, t)
  }
}
abstract class SingleGoalDependentTactic(override val name: String) extends DependentTactic(name) {
  def computeExpr(sequent: Sequent): BelleExpr
  final override def computeExpr(provable: ProvableSig): BelleExpr = {
    require(provable.subgoals.size == 1, "Exactly 1 subgoal expected, but got " + provable.subgoals.size)
    computeExpr(provable.subgoals.head)
  }
}
abstract class LabelledGoalsDependentTactic(override val name: String) extends DependentTactic(name) {
  def computeExpr(provable: ProvableSig, labels: List[BelleLabel]): BelleExpr = throw new BelleThrowable("Not implemented")
  /** Generic computeExpr; prefer overriding computeExpr(Provable) and computeExpr(BelleThrowable) */
  override def computeExpr(v : BelleValue): BelleExpr = try { v match {
    case BelleProvable(provable, Some(labels)) => computeExpr(provable, labels)
    case BelleProvable(provable, None) => computeExpr(provable)
    case e: BelleThrowable => super.computeExpr(e)
  }
  } catch {
    case be: BelleThrowable => throw be
    case t: Throwable => if (DEBUG) t.printStackTrace(); throw new BelleThrowable(t.getMessage, t)
  }
}

/** DependentPositionTactics are tactics that can be [[AtPosition applied at positions]] giving dependent tactics.
  *
  * @see [[AtPosition]] */
abstract case class DependentPositionTactic(name: String) extends NamedBelleExpr with AtPosition[DependentTactic] {
  override def apply(locator: PositionLocator): AppliedDependentPositionTactic = new AppliedDependentPositionTactic(this, locator)
  override def prettyString: String = "DependentPositionTactic(" + name + ")"
  /** Create the actual tactic to be applied at position pos */
  def factory(pos: Position): DependentTactic
}
abstract case class InputTactic(name: String, inputs: List[Any]) extends BelleExpr with NamedBelleExpr {
  def computeExpr(): BelleExpr
  override def prettyString: String =
    s"$name(${inputs.map({case input: Expression => s"{`${input.prettyString}`}" case input => s"{`${input.toString}`}"}).mkString(",")})"
}
abstract class StringInputTactic(override val name: String, val inputs: List[String]) extends BuiltInTactic(name) {
  override def prettyString: String =
    s"$name(${inputs.map(input => s"{`$input`}").mkString(",")})"
}

abstract class DependentPositionWithAppliedInputTactic(private val n: String, val inputs: List[Any]) extends DependentPositionTactic(n) {
  override def apply(locator: PositionLocator): AppliedDependentPositionTacticWithAppliedInput = new AppliedDependentPositionTacticWithAppliedInput(this, locator)
}
class AppliedDependentPositionTacticWithAppliedInput(pt: DependentPositionWithAppliedInputTactic, locator: PositionLocator) extends AppliedDependentPositionTactic(pt, locator) {
  override def prettyString: String =
    s"${pt.name}(${pt.inputs.map({ case input: Expression => s"{`${input.prettyString}`}" case input => s"{`${input.toString}`}"}).mkString(",")},${locator.prettyString})"
}
class AppliedDependentPositionTactic(val pt: DependentPositionTactic, val locator: PositionLocator) extends DependentTactic(pt.name) {
  import Augmentors._
  override def prettyString: String = pt.name + "(" + locator.prettyString + ")"
  final override def computeExpr(v: BelleValue): BelleExpr = try {
    locator match {
      //@note interprets PositionLocator
      case Fixed(pos, shape, exact) => shape match {
        case Some(f) => v match {
          case BelleProvable(provable, _) =>
            require(provable.subgoals.size == 1, "Locator 'fixed with shape' applies only to provables with exactly 1 subgoal")
            //@note (implicit .apply needed to ensure subposition to pos.inExpr
            if ((exact && provable.subgoals.head.sub(pos).contains(f)) ||
              (!exact && UnificationMatch.unifiable(f, provable.subgoals.head.sub(pos).get).isDefined)) {
              pt.factory(pos).computeExpr(v)
            } else {
              throw new BelleThrowable("Formula " + provable.subgoals.head.sub(pos) + " at position " + pos +
                " is not of expected shape " + f)
            }
        }
        case None => pt.factory(pos).computeExpr(v)
      }
      case Find(goal, shape, start, exact) =>
        require(start.isTopLevel, "Start position must be top-level in sequent")
        tryAllAfter(goal, shape, start, exact, null)
      case LastAnte(goal) => pt.factory(v match { case BelleProvable(provable, _) => AntePosition.base0(provable.subgoals(goal).ante.size - 1) })
      case LastSucc(goal) => pt.factory(v match { case BelleProvable(provable, _) => SuccPosition.base0(provable.subgoals(goal).succ.size - 1) })
    }
  } catch {
    //note the following exceptions are likely caused by wrong positioning
    case be: BelleThrowable => locator match {
      case _: Find => throw be
      case Fixed(pos, _, _) => v match {
        case BelleProvable(provable, _) if provable.subgoals.size == 1 =>
          throw new BelleThrowable("Tactic " + prettyString + " may point to wrong position, found " + provable.subgoals.head.sub(pos) + " at position " + locator, be)
        case _ => throw be
      }
    }
    case ex: IndexOutOfBoundsException => throw new BelleThrowable("Position " + locator +
      " may point outside the positions of the goal " + v.prettyString, ex)
    //@note wrap failing assertions etc. so that searchy tactic combinators follow up on the tactic failure
    case t: Throwable => throw new BelleThrowable(t.getMessage, t)
  }

  /** Recursively tries the position tactic at positions at or after pos in the specified provable. */
  private def tryAllAfter(goal: Int, shape: Option[Expression], pos: Position, exact: Boolean,
                          cause: BelleThrowable): DependentTactic = new DependentTactic(name) {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable, _) =>
        if (pos.isIndexDefined(provable.subgoals(goal))) {
          try {
            shape match {
              case Some(f: Formula) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isDefined =>
                pt.factory(pos).computeExpr(v) | tryAllAfter(goal, shape, pos.advanceIndex(1), exact, cause)
              case Some(f: Formula) if !exact && UnificationMatch.unifiable(f, provable.subgoals(goal)(pos.top)).isEmpty =>
                tryAllAfter(goal, shape, pos.advanceIndex(1), exact, new BelleThrowable(s"Formula is not of expected shape", cause))
              case Some(f: Formula) if exact && f == provable.subgoals(goal)(pos.top) =>
                pt.factory(pos).computeExpr(v) | tryAllAfter(goal, shape, pos.advanceIndex(1), exact, cause)
              case Some(f: Formula) if exact && f != provable.subgoals(goal)(pos.top) =>
                tryAllAfter(goal, shape, pos.advanceIndex(1), exact, new BelleThrowable(s"Formula is not of expected shape", cause))
              case Some(t: Term) =>
                val tPos = FormulaTools.posOf(provable.subgoals(goal)(pos.top), e => if (exact) e == t else UnificationMatch.unifiable(e, t).isDefined)
                if (tPos.isEmpty) tryAllAfter(goal, shape, pos.advanceIndex(1), exact, new BelleThrowable(s"Formula is not of expected shape", cause))
                else pt.factory(pos.topLevel ++ tPos.head).computeExpr(v) | tryAllAfter(goal, shape, pos.advanceIndex(1), exact, cause)
              case None =>
                pt.factory(pos).computeExpr(v) | tryAllAfter(goal, shape, pos.advanceIndex(1), exact, cause)
            }
          } catch {
            // also advance if computeExpr already throws a BelleThrowable
            case e: BelleThrowable =>
              val newCause = if (cause == null) new BelleThrowable(s"Dependent position tactic ${pt.prettyString} is not " +
                s"applicable at ${pos.prettyString}", e)
              else new CompoundException(
                new BelleThrowable(s"Dependent position tactic ${pt.prettyString} is not applicable at ${pos.prettyString}", e),
                cause)
              tryAllAfter(goal, shape, pos.advanceIndex(1), exact, newCause)
          }
        } else if (cause == null) {
          throw new BelleThrowable(s"Dependent position tactic ${pt.prettyString} is not applicable at ${pos.prettyString} in ${provable.subgoals(goal).prettyString}")
        } else throw cause
      case _ => pt.factory(pos).computeExpr(v) | tryAllAfter(goal, shape, pos.advanceIndex(1), exact, cause)
    }
  }
}

/** A partial tactic is allowed to leave its subgoals around as unproved */
@deprecated("Replace with something else -- either assertProved or some sort of branch indicator?", "4.2")
case class PartialTactic(child: BelleExpr, label: Option[BelleLabel] = None) extends BelleExpr {
  override def prettyString = label match {
    case Some(theLabel) => s"partial(${child.prettyString})@(${theLabel.prettyString})"
    case None => s"partial(${child.prettyString})"
  }
}

case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr { override def prettyString = "(" + left.prettyString + "&" + right.prettyString + ")" }
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr { override def prettyString = "(" + left.prettyString + "|" + right.prettyString + ")" }
//@note saturate and repeat tactic fully parenthesize for parser
case class SaturateTactic(child: BelleExpr) extends BelleExpr { override def prettyString = "((" + child.prettyString + ")*)" }
case class RepeatTactic(child: BelleExpr, times: Int) extends BelleExpr { override def prettyString = "((" + child.prettyString + ")*" + times + ")" }
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr { override def prettyString = "<( " + children.map(_.prettyString).mkString(", ") + " )" }
/** USubstPatternTactic((form1, us=>t1) :: ... (form2, us=>t2) :: Nil)
  * runs the first tactic `ti` for the unification `us` with the first pattern `formi` that matches the current goal.
  */
case class USubstPatternTactic(options: Seq[(BelleType, RenUSubst => BelleExpr)]) extends BelleExpr { override def prettyString = "case { " + options.mkString(", ") + " }"}

/**
  * OnAll(e)(BelleProvable(p)) == <(e, ..., e) does the same tactic on all branches
  * where e occurs the appropriate number of times, which is `p.subgoals.length` times.
  *
  * @todo eisegesis
  */
case class OnAll(e: BelleExpr) extends BelleExpr { override def prettyString = "doall(" + e.prettyString + ")" }

/**
  * ChooseSome(options, e)(pr) proves `e(o)(pr)` after choosing some option `o` from `options`
  * whose proof with tactic `e` succeeds after supplying argument `o` to `e`.
  * It's usually one of the first options `o` for which `e(o)(pr)` does not fail.
  * Fails if no choice from `options` made `e(o)(pr)` succeed.
  *
  * @param options The (lazy) iterator or stream from which subsequent options `o` will be tried.
  * @param e The tactic generator `e` that will be tried with input `o` on the Provable subsequently
  *          for each of the options `o` in `options` until one is found for which `e(o)` does not fail.
  * @author Andre Platzer
  * @see [[EitherTactic]]
  */
case class ChooseSome[A](options: () => Iterator[A], e: A => BelleExpr) extends BelleExpr { override def prettyString = "dosome(" + e + ")" }


/**
  * Let(abbr, value, inner) alias `let abbr=value in inner` abbreviates `value` by `abbr` in the
  * provable and proceeds with an internal proof by tactic `inner`, resuming to the outer proof by a
  * uniform substitution of `value` for `abbr` of the resulting provable.
  *
  * @see [[ProvableSig.apply(USubst)]]
  * @todo generalize inner to also AtPosition[E]
  */
case class Let(abbr: Expression, value: Expression, inner: BelleExpr) extends BelleExpr {
  require(abbr.kind == value.kind, "Abbreviation and value must be of same kind, but got abbr.kind=" + abbr.kind + " and value.kind=" + value.kind)
  override def prettyString = "let(" + abbr + "=" + value + " in " + inner + ")"
}

/**
  * LetInspect(abbr, instantiator, inner) alias `let abbr := inspect instantiator in inner`
  * postpones the choice for the definition of `abbr` until tactic `inner` finished on the Provable,
  * and asks `instantiator` to choose a value for `abbr` based on that Provable at the end of `inner`.
  * Resumes  to the outer proof by a uniform substitution of `instantiator(result)` for `abbr` of the resulting provable.
  *
  * @see [[ProvableSig.apply(USubst)]]
  * @todo generalize inner to also AtPosition[E]
  * @note abbr should be fresh in the Provable
  */
case class LetInspect(abbr: Expression, instantiator: ProvableSig => Expression, inner: BelleExpr) extends BelleExpr {
  override def prettyString = "let(" + abbr + ":= inspect " + instantiator + " in " + inner + ")"
}

/** Defines a tactic for later execution. */
case class DefTactic(name: String, t: BelleExpr) extends BelleExpr {
  override def prettyString: String = s"tactic $name as (${t.prettyString})"
}

/** Applies the tactic definition `t`. */
case class ApplyDefTactic(t: DefTactic) extends BelleExpr {
  override def prettyString: String = t.name
}

/** Defines an expression (function or predicate) for later expansion. */
case class DefExpression(exprDef: Formula) extends BelleExpr {
  assert(exprDef match {
    case Equal(FuncOf(_, _), _) => true
    case Equiv(PredOf(_, _), _) => true
    case _ => false
  }, s"Expected either function definition of shape f(x)=t or predicate definition of shape p(x) <-> q, but got ${exprDef.prettyString}")
  override def prettyString: String = s"def {`${exprDef.prettyString}`}"
}

/** Expands a function or predicate. */
case class ExpandDef(expr: DefExpression) extends BelleExpr {
  override def prettyString: String = s"expand {`${expr.exprDef match {
    case Equal(fn@FuncOf(_, _), _) => fn.prettyString
    case Equiv(p@PredOf(_, _), _) => p.prettyString
  }}`}"
}

@deprecated("Does not work with useAt, which was the only point. There's also no way to print/parse ProveAs correctly, and scoping is global. So ProveAs should be replaced with something more systematic.", "4.2")
case class ProveAs(lemmaName: String, f: Formula, e: BelleExpr) extends BelleExpr {
  override def prettyString: String = s"proveAs(${lemmaName})"
}

/**
 * Bellerophon expressions that are values.
 */
trait BelleValue {
  def prettyString: String = toString
}
case class BelleProvable(p : ProvableSig, label: Option[List[BelleLabel]] = None) extends BelleExpr with BelleValue {
  if(label.nonEmpty) insist(label.get.length == p.subgoals.length, s"Length of label set (${label.get.length}) should equal number of remaining subgoals (${p.subgoals.length}")
  override def toString: String = p.prettyString
  override def prettyString: String = p.prettyString
}

/** To communicate proof IDs of subproofs opened in the spoon-feeding interpreter in Let between requests.
  * NOT TO BE USED FOR ANYTHING ELSE */
case class BelleSubProof(id: Int) extends BelleValue

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Labels
////////////////////////////////////////////////////////////////////////////////////////////////////
trait BelleLabel {
  protected val LABEL_DELIMITER: String = ":"
  def prettyString: String
}
case class BelleTopLevelLabel(label: String) extends BelleLabel {
  require(!label.contains(LABEL_DELIMITER), s"Label should not contain the sublabel delimiter $LABEL_DELIMITER")
  override def prettyString: String = label
}
case class BelleSubLabel(parent: BelleLabel, label: String)  extends BelleLabel {
  require(!label.contains(LABEL_DELIMITER), s"Label should not contain the sublabel delimiter $LABEL_DELIMITER")
  override def prettyString: String = parent.prettyString + LABEL_DELIMITER + label
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/** @todo eisegesis -- simple types */
@deprecated("remove")
trait BelleType
@deprecated("remove")
case class TheType() extends BelleType
/** @todo Added because SequentTypes are needed for unification tactics. */
@deprecated("remove")
case class SequentType(s : Sequent) extends BelleType

