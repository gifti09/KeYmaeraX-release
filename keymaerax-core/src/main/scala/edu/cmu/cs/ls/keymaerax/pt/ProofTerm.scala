package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

/**
 * A Proof Term is a syntactic internalization of a proof of a differential dynamic logic theorem.
 * Proof Terms can be converted to Provables by the [[ProofChecker]].
 * Created by nfulton on 10/15/15.
 * @see [[ProofChecker]]
 */
sealed abstract class ProofTerm() {
  def prettyString: String = this.toString //@todo leave this abstract and over-ride in all the cases below.
}
//@todo support also positional stuff and proof terms for entire provables...
case class dLConstant(label: String) extends ProofTerm
case class FOLRConstant(f : Formula) extends ProofTerm
case class AndTerm(left: ProofTerm, right: ProofTerm) extends ProofTerm
case class ApplicationTerm(left: ProofTerm, premise: Formula, right: ProofTerm) extends ProofTerm
case class RightEquivalence(left: ProofTerm, premise: Formula, right: ProofTerm) extends ProofTerm
case class LeftEquivalence(left: ProofTerm, premise: Formula, right: ProofTerm) extends ProofTerm
case class CTTerm(child: ProofTerm, premise: Equal, substitution: USubst) extends ProofTerm
case class CQTerm(child: ProofTerm, premise: Equal, substitution: USubst) extends ProofTerm
case class CETerm(child: ProofTerm, premise: Equiv, substitution: USubst) extends ProofTerm
case class UsubstTerm(child: ProofTerm, premise: Formula, substitution: USubst) extends ProofTerm
//@todo eisegesis theory alllows a set of renamings. Also, make sure UniformRenamings are sufficient for all proofs.
case class RenamingTerm(child: ProofTerm, premise: Formula, what: Variable, repl: Variable) extends ProofTerm
/** Witness for rule application. */
case class RuleApplication(child: ProofTerm, ruleName: String, subgoal: Int) extends ProofTerm //@todo add to theory.
case class UsubstProvableTerm(child: ProofTerm, substitution: USubst) extends ProofTerm
/** @todo replaces dLConstant so we can distinguish between rule applications and axiom applications. */
case class AxiomTerm(name: String) extends ProofTerm
case class RuleTerm(name: String) extends ProofTerm
/** @todo replace this with a proof term construction. */
case class ForwardNewConsequenceTerm(child: ProofTerm, newConsequence: Sequent, rule: Rule) extends ProofTerm
/** @todo replace this with a proof term construction. */
case class ProlongationTerm(child: ProofTerm, prolongation: PTProvable) extends ProofTerm
case class NoProof() extends ProofTerm