package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.btactics.DerivedRuleInfo
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable

/**
 * ProofChecker maps a proof term to the Provable it proves.
 * {{{
 *   ProofChecker : ProofTerm * Formula => Provable
 * }}}
 * with a successful answer if the proof indeed checked successfully.
 * Not soundness-critical, because the proof checker compiles the proof term into
 * subsequent proof rule and axiom applications in the [[edu.cmu.cs.ls.keymaerax.core prover core]].
 * Created by nfulton on 10/15/15.
  *
  * @author Nathan Fulton
 * @see [[ProofTerm]]
 * @see [[ProvableSig]]
 */
object ProofChecker {
  private val tool = new edu.cmu.cs.ls.keymaerax.tools.Mathematica()

  private def goalSequent(phi : Formula) = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(phi))
  private def proofNode(phi : Formula) = ProvableSig.startProof(goalSequent(phi))

  /**
   * Converts proof term e for goal phi into a Provable iff e indeed justifies phi.
    *
    * @todo could remove phi except no more contract then
   */
  def apply(e: ProofTerm, phi: Formula) : Option[ProvableSig] = {
    e match {
      case dLConstant(label) => Some(
        ProvableSig.startProof(goalSequent(phi))
        (ProvableSig.axioms(label), 0)
      )

      case FOLRConstant(f) => {
        val node = proofNode(phi)
        Some(proveBy(node, QE & done))
      }

      case AndTerm(e, d) => phi match {
        case And(varphi, psi) => {
          val varphiCert = ProofChecker(e, varphi)
          val psiCert = ProofChecker(d, psi)
          (varphiCert, psiCert) match {
            case (Some(varphiCert), Some(psiCert)) => {
              //This is the ^R schematic proof rule referred to in the theory proof.
              val andR = edu.cmu.cs.ls.keymaerax.core.AndRight(SuccPos(0))
              Some(
                ProvableSig.startProof(goalSequent(phi))
                  (andR, 0)
                  // left branch
                  (varphiCert, 0)
                //right branch
                  (psiCert, 0)
              )
            }
            case _ => None
          }
        }
        case _ => None
      }

      case ApplicationTerm(e, psi, d) => {
        val implCert = ProofChecker(e, Imply(psi, phi))
        val psiCert = ProofChecker(d, psi)

        if(implCert.isDefined && implCert.get.isProved && psiCert.isDefined && psiCert.get.isProved)
          //@todo Eisegesis. Adopt implementation or adopt proof so that they are the same.
          Some(
            ProvableSig.startProof(goalSequent(phi))
              (Cut(Imply(psi, phi)), 0)
              (HideRight(SuccPos(0)), 1)(implCert.get, 1) // hide phi and prove psi -> phi using proof produced by IH
              (Cut(psi), 0)
              (HideLeft(AntePos(0)), 1)(HideRight(SuccPos(0)), 1)(psiCert.get, 1) // have phi -> psi |- phi, psi. Hides antecendent and phi, and proves psi by IH.
              (ImplyLeft(AntePos(0)), 0)
              (Close(AntePos(0), SuccPos(1)), 0)
              (Close(AntePos(1), SuccPos(0)), 0)
          )
        else None
      }

      case LeftEquivalence(e, psi, d) => {
        val equivCert = ProofChecker(e, Equiv(psi, phi))
        val psiCert   = ProofChecker(d, psi)

        if(equivCert.isDefined && equivCert.get.isProved && psiCert.isDefined && psiCert.get.isProved) {
          /* Game plan:
           *     - Transform to the goal psi<->phi, phi |- psi (readyForRewrite)
           *     - Rewrite to phi |- phi using equality rewriting tactics and then close the proof
           *     - Extract provable (rewritingWitness)
           *     - apply tactic provable to the remaining goal on the provable with the desired conclusion (readyForRewrite)
           */
          //@todo Eisegesis. Adopt implementation or adopt proof so that they are the same.
          val readyForRewrite = (
            ProvableSig.startProof(goalSequent(phi))
            (Cut(Equiv(psi, phi)), 0)
            (HideRight(SuccPos(0)), 1)(equivCert.get, 1) // hide phi and prove psi <-> phi using proof produced by IH
            (Cut(psi), 0)
            (HideLeft(AntePos(0)), 1)(HideRight(SuccPos(0)), 1)(psiCert.get, 1) // have phi <-> psi |- phi, psi. Hides antecendent and phi, and proves psi by IH.
            (CommuteEquivLeft(AntePos(0)), 0)
          )

          //@todo is there a better way of combining scheduled tactics with direct manipulation proofs?
          //@todo and/or is there a better way of doing equivalence rewriting with direct manipulation proofs?
          val rewritingWitness = {
            val node = readyForRewrite.subgoals.last
            proveBy(node, eqL2R(-1)(1) & closeId)
          } ensuring(r => r.isProved)

          Some(readyForRewrite(rewritingWitness, 0))
        }
        else None
      }

      case RightEquivalence(e, psi, d) => {
        val equivCert = ProofChecker(e, Equiv(psi, phi))
        val psiCert   = ProofChecker(d, psi)
        //@note in principle could use CommuteEquivRight to reduce to LeftEquivalence case

        if(equivCert.isDefined && equivCert.get.isProved && psiCert.isDefined && psiCert.get.isProved) {
          /* Game plan:
           *     - Transform to the goal psi<->phi, phi |- psi (readyForRewrite)
           *     - Rewrite to phi |- phi using equality rewriting tactics and then close the proof
           *     - Extract provable (rewritingWitness)
           *     - apply tactic provable to the remaining goal on the provable with the desired conclusion (readyForRewrite)
           */
          //@todo Eisegesis. Adopt implementation or adopt proof so that they are the same.
          val readyForRewrite = (
            ProvableSig.startProof(goalSequent(phi))
            (Cut(Equiv(psi, phi)), 0)
            (HideRight(SuccPos(0)), 1)(equivCert.get, 1) // hide phi and prove psi <-> phi using proof produced by IH
            (Cut(psi), 0)
            (HideLeft(AntePos(0)), 1)(HideRight(SuccPos(0)), 1)(psiCert.get, 1) // have phi <-> psi |- phi, psi. Hides antecendent and phi, and proves psi by IH.
            (CommuteEquivLeft(AntePos(0)), 0)
          )

          //@todo is there a better way of combining scheduled tactics with direct manipulation proofs?
          //@todo and/or is there a better way of doing equivalence rewriting with direct manipulation proofs?
          val rewritingWitness = {
            val node = readyForRewrite.subgoals.last
            proveBy(node, eqL2R(-1)(1) & closeId)
          } ensuring(r => r.isProved)

          Some(readyForRewrite(rewritingWitness, 0))
        }
        else None
      }

      case UsubstTerm(e, phiPrime, usubst) => {
        val phiPrimeCert = ProofChecker(e, phiPrime)
        if(phiPrimeCert.isDefined && phiPrimeCert.get.isProved) {
          val goalS = goalSequent(phi)
          Some(??? /*@todo
            Provable.startProof(goalS)
            (UniformSubstitutionRule(usubst, goalSequent(phiPrime)), 0)
            (phiPrimeCert.get, 0)
          */)
        }
        else None
      }

      case RenamingTerm(e, phiPrime, what, repl) => {
        val phiPrimeCert = ProofChecker(e, phiPrime)
        if(phiPrimeCert.isDefined && phiPrimeCert.get.isProved) {
          val goalS = goalSequent(phi)
          Some( UniformRenaming.UniformRenamingForward(ProvableSig.startProof(goalS), what, repl) )
        }
        else None
      }

        //@todo There's a question whether flat usubst "triple" would be better in the long term than one specialized to the names in rule.
      case CTTerm(e, premise, usubst) => {
        val equalityCert = ProofChecker(e, premise)
        if(equalityCert.isDefined && equalityCert.get.isProved) Some(
          ProvableSig.startProof(goalSequent(phi))
          (DerivedRuleInfo("CT term congruence").provable(usubst), 0)
          (equalityCert.get, 0)
        )
        else None
      }

      case CQTerm(e, premise, usubst) => {
        val equalityCert = ProofChecker(e, premise)
        if(equalityCert.isDefined && equalityCert.get.isProved) Some(
          ProvableSig.startProof(goalSequent(phi))
          (ProvableSig.rules("CQ term congruence")(usubst), 0)
          (equalityCert.get, 0)
        )
        else None
      }

      case CETerm(e, premise, usubst) => {
        val equalityCert = ProofChecker(e, premise)
        if(equalityCert.isDefined && equalityCert.get.isProved) Some(
          ProvableSig.startProof(goalSequent(phi))
          (ProvableSig.rules("CE congruence")(usubst), 0)
          (equalityCert.get, 0)
        )
        else None
      }
    }
  } ensuring(r => r.isEmpty || r.get.conclusion == goalSequent(phi), "Resulting Provable proves given formula if defined for " + phi + " : " + e)
}
