package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics.toSingleFormula
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.CounterExampleTool

import scala.language.postfixOps

/**
 * Implementation: Tactics that execute and use the output of tools.
 * Also contains tactics for pre-processing sequents.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
private object ToolTactics {
  /** Performs QE and fails if the goal isn't closed. */
  def fullQE(order: List[NamedSymbol] = Nil)(qeTool: QETool): BelleExpr = {
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    Idioms.NamedTactic("QE",
//      DebuggingTactics.recordQECall() &
      (alphaRule*) &
        (varExhaustiveEqL2R('L)*) &
        (tryClosePredicate('L)*) & (tryClosePredicate('R)*) &
      Idioms.?(toSingleFormula & FOQuantifierTactics.universalClosure(order)(1) & rcf(qeTool)) &
      DebuggingTactics.done("QE was unable to prove: invalid formula")
  )}
  def fullQE(qeTool: QETool): BelleExpr = fullQE()(qeTool)

  /** Performs QE and allows the goal to be reduced to something that isn't necessarily true.
    * @note You probably want to use fullQE most of the time, because partialQE will destroy the structure of the sequent
    */
  def partialQE(qeTool: QETool) = {
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    Idioms.NamedTactic("pQE",
      toSingleFormula & rcf(qeTool)
    )
  }

  /** Performs Quantifier Elimination on a provable containing a single formula with a single succedent. */
  def rcf(qeTool: QETool) = TacticFactory.anon ((sequent: Sequent) => {
    assert(sequent.ante.isEmpty && sequent.succ.length == 1, "Provable's subgoal should have only a single succedent.")
    require(sequent.succ.head.isFOL, "QE only on FOL formulas")

    //Run QE and extract the resulting provable and equivalence
    //@todo how about storing the lemma, but also need a way of finding it again
    //@todo for storage purposes, store rcf(lemmaName) so that the proof uses the exact same lemma without
    val qeFact = core.Provable.proveArithmetic(qeTool, sequent.succ.head).fact
    val Equiv(_, result) = qeFact.conclusion.succ.head

    ProofRuleTactics.cutLR(result)(SuccPosition(1)) <(
      (close | skip) partial,
      equivifyR(1) & commuteEquivR(1) & by(qeFact)
      )
  })

  /** @see [[TactixLibrary.transform()]] */
  def transform(to: Formula)(tool: QETool with CounterExampleTool): DependentPositionWithAppliedInputTactic = "transform" byWithInput (to, (pos: Position, sequent: Sequent) => {
    require(pos.isTopLevel, "transform only at top level")
    require(sequent(pos.checkTop).isFOL, "transform only on first-order formulas")

    val modalHide = (alphaRule*) & ("modalHide" by ((mhsequent: Sequent) => {
      mhsequent.ante.indices.map(i => if (mhsequent(AntePos(i)).isFOL) skip else hide(AntePos(i))).reduceLeftOption(_&_).getOrElse(skip) &
      mhsequent.succ.indices.map(i => if (mhsequent(SuccPos(i)).isFOL) skip else hide(SuccPos(i))).reduceLeftOption(_&_).getOrElse(skip)
    }))

    //@note if we have a counterexample we can try some smart hiding to make QE easier
    def cex = {
      val orig = sequent.sub(pos).getOrElse(throw new IllegalArgumentException(s"Sequent $sequent at position $pos is not a formula")).asInstanceOf[Formula]
      if (pos.isSucc) tool.findCounterExample(Imply(to, orig))
      else tool.findCounterExample(Imply(orig, to))
    }

    //@note assumes that modalHide is called first
    val smartHide = "smartHide" by ((shsequent: Sequent) => {
      val theCex = cex
      val theCexVars = theCex.get.keySet.filter(x => x.isInstanceOf[Variable]).map(x => x.asInstanceOf[Variable])
      shsequent.ante.indices.reverse.map(i =>
        if (StaticSemantics(shsequent(AntePos(i))).fv.intersect(theCexVars).isEmpty) hide(AntePos(i))
        else skip).reduceLeftOption(_&_).getOrElse(skip) &
      shsequent.succ.indices.reverse.map(i =>
        if (StaticSemantics(shsequent(SuccPos(i))).fv.intersect(theCexVars).isEmpty) hide(SuccPos(i))
        else skip).reduceLeftOption(_&_).getOrElse(skip)
    })


    cutLR(to)(pos) <(
      /* c */ skip,
      //@note first try to prove only the transformation, then with smart hiding, if all that fails, full QE on all FOL formulas
      /* c->d */ (cohide(pos) & QE) | (modalHide & ((smartHide & QE) | QE))
      )
  })

  /* Rewrites equalities exhaustively with hiding, but only if left-hand side is a variable */
  private def varExhaustiveEqL2R: DependentPositionTactic =
    "Find Left and Replace Left with Right" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(fml@Equal(_: Variable, _)) => EqualityTactics.exhaustiveEqL2R(pos) & hideL(pos, fml)
    })

  /* Tries to close predicates by identity, hide if unsuccessful (QE cannot handle predicate symbols) */
  private def tryClosePredicate: DependentPositionTactic = "Try close predicate" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(p@PredOf(_, _)) => closeId | (hide(pos) partial)
  })
}
