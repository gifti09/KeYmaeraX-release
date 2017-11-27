package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

/**
 * A Proof Term is a syntactic internalization of a proof of a differential dynamic logic theorem.
 * Proof Terms can be converted to Provables by the [[ProofChecker]].
 * Created by nfulton on 10/15/15.
 * @see [[ProofChecker]]
 * @author Nathan Fulton
 * @author Brandon Bohrer         
 */
sealed abstract class ProofTerm() {

  /* HACK: Code elsewhere uses equality tests on ProvableSigs under the assumption that equality depends only on the conclusion and subgoals.
  * we make this more true by considering all proofterms equal to each other.
  * We should consider changing the equality function on ProvableSig, but this is a less invasive change
  * */
  override def equals(other:Any): Boolean = {
    other match {
      case pt: ProofTerm => true
      case _ => false
    }
  }

  def prettyString: String = this.toString

  // Number of constructors in the proof term
  def numCons:Int = {
    this match {
      case _: FOLRConstant => 1
      case _: AxiomTerm => 1
      case _: RuleTerm => 1
      case _: NoProof => 1
      case UsubstProvableTerm(child, _) => child.numCons + 1
      case RuleApplication(child, _, _, _, _) => child.numCons + 1
      case ProlongationTerm(child, pro) => child.numCons + pro.numCons + 1
      case ForwardNewConsequenceTerm(child, _, _) => child.numCons + 1
      case Sub(child, sub, _) => child.numCons + sub.numCons + 1
      case StartProof(phi) => 1
    }
  }

  // All axioms that appear in the proof
  def axiomsUsed:Set[String] = {
    this match {
      case AxiomTerm(name) => Set(name)
      case _ : FOLRConstant => Set()
      case _ : RuleTerm => Set()
      case _ : NoProof => Set()
      case _ : StartProof => Set()
      case UsubstProvableTerm(child, _) => child.axiomsUsed
      case RuleApplication(child, _, _, _, _) => child.axiomsUsed
      case ProlongationTerm(child, pro) => child.axiomsUsed ++ pro.axiomsUsed
      case ForwardNewConsequenceTerm(child, _, _) => child.axiomsUsed
      case Sub(child, sub, _) => child.axiomsUsed ++ sub.axiomsUsed

    }
  }

  // All rules that appear in the proof
  def rulesUsed:Set[String] = {
    this match {
      case RuleTerm(name) => Set(name)
      case RuleApplication(child, name, _, _, _) => child.rulesUsed ++ Set(name)
      case _ : AxiomTerm => Set()
      case _ : FOLRConstant => Set()
      case _ : NoProof => Set()
      case _ : StartProof => Set()
      case UsubstProvableTerm(child, _) => child.rulesUsed
      case ProlongationTerm(child, pro) => child.rulesUsed ++ pro.rulesUsed
      case ForwardNewConsequenceTerm(child, _, _) => child.rulesUsed
      case Sub(child, sub, _) => child.rulesUsed ++ sub.rulesUsed
    }
  }


  // All first-order logic assumptions that appear in the proof
  def arithmeticGoals:Set[Formula] = {
    this match {
      case FOLRConstant(f) => Set(f)
      case _ : RuleTerm => Set()
      case _ : AxiomTerm => Set()
      case _ : NoProof => Set()
      case _ : StartProof => Set()
      case UsubstProvableTerm(child, _) => child.arithmeticGoals
      case ProlongationTerm(child, pro) => child.arithmeticGoals ++ pro.arithmeticGoals
      case ForwardNewConsequenceTerm(child, _, _) => child.arithmeticGoals
      case RuleApplication(child, name, _, _, _) => child.arithmeticGoals
      case Sub(child, sub, _) => child.arithmeticGoals ++ sub.arithmeticGoals
    }
  }

  val wordSize = 8

  private def expBytesEstimate(f:Expression):Int = {
    f match {
      case _ : Atomic => 2*wordSize // poor estimate because different numbers of arguments of different types
      case e : UnaryComposite => 2*wordSize + expBytesEstimate(e.child)
      case e : BinaryComposite => 3*wordSize + expBytesEstimate(e.left) + expBytesEstimate(e.right)
      case e : ApplicationOf => 3*wordSize + 6*wordSize + expBytesEstimate(e.child)//function is six or so words?
      case ns : NamedSymbol => 3*wordSize //also poor estimate
      case q : Quantified => 3*wordSize + expBytesEstimate(q.child) //also poor estimate
      case m : Modal => 3*wordSize + expBytesEstimate(m.child) + expBytesEstimate(m.program)
      case ode : ODESystem => 3*wordSize + expBytesEstimate(ode.constraint) + expBytesEstimate(ode.ode)
    }
  }

  private def subBytesEstimate(subst: USubst):Int = {
    subst.subsDefsInput.foldLeft(0)((acc,pair) =>acc + expBytesEstimate(pair.what) + expBytesEstimate(pair.repl))
  }

  private def sequentBytesEstimate(sequent: Sequent):Int = {
    sequent.succ.foldLeft(
      sequent.ante.foldLeft(0)((acc, fml) => acc + expBytesEstimate(fml)))((acc, fml) => acc + expBytesEstimate(fml))
  }

  private def ruleBytesEstimate(rule: Rule):Int = {
    wordSize
  }

  private val intSizeEstimate = 2*wordSize

  private def seqBytesEstimate[T](s:Seq[T]):Int = {
    (2 + s.length)*wordSize
  }

  // Estimate of the size in bytes of a proof term
  def bytesEstimate:Int = {
        this match {
      case FOLRConstant(f) => expBytesEstimate(f) + 2*wordSize // over-estimates due to structure sharing
      case RuleTerm(_) => 2*wordSize // Assume names are interned
      case AxiomTerm(_) => 2*wordSize
      case _ : NoProof => wordSize
      case StartProof(seq) => 2*wordSize + sequentBytesEstimate(seq)
      case UsubstProvableTerm(child, sub) => 3*wordSize + child.bytesEstimate + subBytesEstimate(sub)
      case ProlongationTerm(child, pro) => 3*wordSize + child.bytesEstimate + pro.bytesEstimate
      case ForwardNewConsequenceTerm(child, con, rule) => 4*wordSize + child.bytesEstimate + sequentBytesEstimate(con) + ruleBytesEstimate(rule)
      case RuleApplication(child,name,subgoal,poses, expArgs) => 6*wordSize + child.bytesEstimate + intSizeEstimate + seqBytesEstimate(poses) + seqBytesEstimate(expArgs)
      case Sub(child, sub, i) => 4*wordSize + child.bytesEstimate + sub.bytesEstimate + intSizeEstimate
    }
  }
}

case class FOLRConstant(f : Formula) extends ProofTerm

/** Witness for rule application. */
case class RuleApplication(child: ProofTerm, ruleName: String, subgoal: Int, sequentPositions: Seq[SeqPos], expArgs:Seq[Expression]) extends ProofTerm //@todo add to theory.
/* @todo: could unify RuleTerm and AxiomTerm */
case class RuleTerm(name: String) extends ProofTerm

case class UsubstProvableTerm(child: ProofTerm, substitution: USubst) extends ProofTerm

case class AxiomTerm(name: String) extends ProofTerm


case class ForwardNewConsequenceTerm(child: ProofTerm, newConsequence: Sequent, rule: Rule) extends ProofTerm

case class ProlongationTerm(child: ProofTerm, prolongation: ProofTerm) extends ProofTerm

case class StartProof(phi:Sequent) extends ProofTerm

case class NoProof() extends ProofTerm

case class Sub(child:ProofTerm, sub:ProofTerm, idx: Int) extends ProofTerm
