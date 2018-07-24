package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.Expression

import scala.collection.immutable._

/**
  * @note Needs some work because the constructors for Belle expressions are far more diverse than
  *       the constructors for KeYmaera X expressions
  */
sealed trait BelleOpSpec {
  val terminal: BelleTerminal
  val precedence: Int
  val leftAssoc: Boolean

  def <(other: BelleOpSpec) = this.precedence < other.precedence
  def >(other: BelleOpSpec) = this.precedence > other.precedence
  def ==(other: BelleOpSpec) = this.precedence == other.precedence
}
case class BelleUnaryOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean) extends BelleOpSpec
case class BelleBinaryOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean) extends BelleOpSpec
case class BelleBranchingOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (Seq[BelleExpr]) => BelleExpr) extends BelleOpSpec
case class BelleSaturatingOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (BelleExpr, BelleType) => BelleExpr) extends BelleOpSpec
case class BelleRepeatOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (BelleExpr, Int, BelleType) => BelleExpr) extends BelleOpSpec
case class BelleUSubstOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (Seq[(BelleType, RenUSubst => BelleExpr)]) => BelleExpr) extends BelleOpSpec
case class BelleLetOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (Expression, Expression, BelleExpr) => BelleExpr) extends BelleOpSpec
case class BelleDefTacticOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (String, BelleExpr) => BelleExpr) extends BelleOpSpec

case class BelleUnitOpSpec[T,S](terminal: BelleTerminal, precedence:Int, leftAssoc: Boolean, constructor: T => S) extends BelleOpSpec

object BelleOpSpec {
  private val none = PSEUDO

  val position = BelleUnitOpSpec(none, 100, false, (x:Any) => ???)

  val base     = BelleUnitOpSpec(none, 0, false, (s:String) => ???)
  val seq      = BelleBinaryOpSpec(SEQ_COMBINATOR,    200, false)
  val either   = BelleBinaryOpSpec(EITHER_COMBINATOR, 220, false)
  val after   = BelleBinaryOpSpec(AFTER_COMBINATOR, 210, false)
  val star     = BelleUnaryOpSpec(KLEENE_STAR,        150, false)
  val saturate = BelleSaturatingOpSpec(SATURATE, 150, false, (child: BelleExpr, annotation: BelleType) => SaturateTactic.apply(child))
  val repeat   = (i: Int) => BelleRepeatOpSpec(N_TIMES(i), 150, false, (child: BelleExpr, times: Int, annotation: BelleType) => RepeatTactic.apply(child, times))
  val branch   = BelleBranchingOpSpec(BRANCH_COMBINATOR, 100, false, BranchTactic.apply)
  val partial  = BelleUnaryOpSpec(PARTIAL, 300, false)
  val onall    = BelleUnaryOpSpec(ON_ALL, 100, false)
  val usubst   = BelleUSubstOpSpec(US_MATCH, 100, false, USubstPatternTactic.apply)
  val let      = BelleLetOpSpec(LET, 100, false, Let.apply)
  val defTactic      = BelleDefTacticOpSpec(TACTIC, 100, false, DefTactic.apply)

  def op(e : BelleExpr): BelleOpSpec = e match {
    case e:SeqTactic      => seq
    case e:EitherTactic   => either
    case e:AfterTactic   => after
    case e:SaturateTactic => star
    case e:RepeatTactic   => repeat(e.times)
    case e:PartialTactic  => partial
    case e:BranchTactic => branch
    case e:OnAll => onall
    case e:USubstPatternTactic => usubst
    case e:BuiltInTactic       => base
    case e:AppliedPositionTactic => base
    case e:AppliedDependentPositionTactic => base
    case _: DefTactic => defTactic
    case _: Let => let
    case _ => base
  }
}
