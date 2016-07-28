package cbcpsold

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Lemma}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory

/**
  * Created by Andreas on 11.11.2015.
  */

case class ComponentProof(invariant: Formula, indInit: Lemma, indUseCase: Lemma, indStep: Lemma) {

//  require(invariant != null && indInit != null && indUseCase != null && indStep != null,
//    "proof data incomplete")

  def getTactic: BelleExpr = ComponentProof.getTactic(this)

  def isComplete = invariant != null && indInit != null && indUseCase != null && indStep != null
}

object ComponentProof {
  val preTactic = andLi *@ TheType() & implyRi

  def apply(invariant: Formula, indInitName: String, indUseCaseName: String, indStepName: String): ComponentProof = {
    val lemmaDB = LemmaDBFactory.lemmaDB
    val initId = new lemmaDB.LemmaID(indInitName)
    val usecaseId = new lemmaDB.LemmaID(indUseCaseName)
    val stepId = new lemmaDB.LemmaID(indStepName)
    require(lemmaDB.contains(initId), "init lemma does not exist")
    require(lemmaDB.contains(usecaseId), "use case lemma does not exist")
    require(lemmaDB.contains(stepId), "step lemma does not exist")

    ComponentProof(invariant, lemmaDB.get(initId).get, lemmaDB.get(usecaseId).get, lemmaDB.get(stepId).get)
  }

  def apply(invariant: Formula, indInit: BelleExpr, indUseCase: BelleExpr, indStep: BelleExpr): ComponentProof = {
    //    TactixLibrary.proveBy()
    null
  }

  def getTactic(invariant: Formula, indInit: Lemma, indUseCase: Lemma, indStep: Lemma): BelleExpr = {
    getTactic(ComponentProof(invariant, indInit, indUseCase, indStep))
  }

  def getTactic(inv: Formula, init: BelleExpr, useCase: BelleExpr, step: BelleExpr): BelleExpr =
    implyR('R) & loop(inv)('R) < (
      (preTactic & init),
      (preTactic & useCase),
      (preTactic & step)
      )


  def getTactic(cp: ComponentProof): BelleExpr = getTactic(cp.invariant, TactixLibrary.by(cp.indInit), TactixLibrary.by(cp.indUseCase), TactixLibrary.by(cp.indStep))

}

