package cbcps

import java.io._

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import java.text.Normalizer.Form

import Utility._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.LemmaID
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedAxioms, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TreeForm.Var
import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXPrettyPrinter}
import ProofHelper._
import sun.misc.FloatingDecimal.BinaryToASCIIConverter

import scala.collection.immutable._
import scala.collection.mutable
import scala.collection.mutable.LinkedHashMap

/**
  * The contract of a component and its interface.
  * Comprises a component and its interface, pre- and post-conditions,
  * the invariant used to verify the contract, and
  * lemmas for verifying baseCase, useCase and step.
  * Created by andim on 25.07.2016.
  *
  * @param component     The component.
  * @param interface     The interface.
  * @param pre           The contracts precondition.
  * @param post          The contracts postcondition.
  * @param invariant     The invariant used to verify the contract.
  * @param baseCaseLemma The lemma used to verify the baseCase. Can be [[None]].
  * @param useCaseLemma  The lemma used to verify the useCase. Can be [[None]].
  * @param stepLemma     The lemma used to verify the step. Can be [[None]].
  */
abstract class Contract(
                         val component: Component,
                         val interface: Interface,
                         val pre: Formula,
                         val post: Formula,
                         val invariant: Formula,
                         var baseCaseLemma: Option[Lemma] = None,
                         var useCaseLemma: Option[Lemma] = None,
                         var stepLemma: Option[Lemma] = None
                       ) {
  require(Contract.admissible(component, interface),
    "interface is NOT admissible for component")
  baseCaseLemma match {
    case Some(l) => verifyBaseCase(l, false)
      require(isBaseCaseVerified(), "provided lemma must verify base case")
    case _ =>
  }
  useCaseLemma match {
    case Some(l) => verifyUseCase(l, false)
      require(isUseCaseVerified(), "provided lemma must verify use case")
    case _ =>
  }
  stepLemma match {
    case Some(l) => verifyStep(l, false)
      require(isStepVerified(), "provided lemma must verify step")
    case _ =>
  }

  /**
    * Returns a list of proof goals that have to be verified to proof the components contract.
    * Should be avoided, rather use [[baseCaseProofGoal()]], [[useCaseProofGoal()]] and [[stepProofGoal()]].
    *
    * @return An [[IndexedSeq]] of proof goals, i.e. sequents.
    */
  def proofGoals(): IndexedSeq[Sequent]

  /**
    * Returns the proof goal that has to be verified to proof the base case of loop induction.
    *
    * @return The baseCase proof goal.
    */
  def baseCaseProofGoal() = proofGoals()(0)

  /**
    * Returns the proof goal that has to be verified to proof the use case of loop induction.
    *
    * @return The useCase proof goal.
    */
  def useCaseProofGoal() = proofGoals()(1)

  /**
    * Returns the proof goal that has to be verified to proof the step of loop induction.
    *
    * @return The step proof goal.
    */
  def stepProofGoal() = proofGoals()(2)

  /**
    * Checks if the baseCase of loop induction was verified.
    * This is the case, if a lemma was stored as baseCaseLemma.
    *
    * @return True, if the baseCase of loop induction as verified.
    */
  def isBaseCaseVerified(): Boolean = baseCaseLemma match {
    case Some(l) => true
    case _ => false
  }

  /**
    * Checks if the useCase of loop induction was verified.
    * This is the case, if a lemma was stored as useCaseLemma.
    *
    * @return True, if the useCase of loop induction as verified.
    */
  def isUseCaseVerified(): Boolean = useCaseLemma match {
    case Some(l) => true
    case _ => false
  }

  /**
    * Checks if the step of loop induction was verified.
    * This is the case, if a lemma was stored as stepLemma.
    *
    * @return True, if the step of loop induction as verified.
    */
  def isStepVerified(): Boolean = stepLemma match {
    case Some(l) => true
    case _ => false
  }

  /**
    * Tries to verify the baseCase with the provided lemma.
    * Fails if the baseCase was verified already.
    *
    * @param l The lemma used to attempt to verify the baseCase.
    * @return True, if the baseCase could be verified.
    */
  def verifyBaseCase(l: Lemma): Boolean = verifyBaseCase(l, true)

  /**
    * Tries to verify the baseCase with the provided lemma.
    * The lemma is stored in the contract, if successfull.
    * Only fails if the baseCase was verified already and check was true.
    *
    * @param l     The lemma used to attempt to verify the baseCase.
    * @param check If check is false, it will not be checked if the baseCase was already verified.
    * @return True, if the baseCase could be verified.
    */
  private def verifyBaseCase(l: Lemma, check: Boolean): Boolean = {
    require(!check || !isBaseCaseVerified(), "base case already verified")
    if (TactixLibrary.proveBy(baseCaseProofGoal(), by(l)).isProved) {
      baseCaseLemma = Some(l)
      true
    }
    else {
      baseCaseLemma = None
      false
    }
  }

  /**
    * Tries to verify the useCase with the provided lemma.
    * Fails if the useCase was verified already.
    *
    * @param l The lemma used to attempt to verify the useCase.
    * @return True, if the useCase could be verified.
    */
  def verifyUseCase(l: Lemma): Boolean = verifyUseCase(l, true)

  /**
    * Tries to verify the useCase with the provided lemma.
    * The lemma is stored in the contract, if successfull.
    * Only fails if the useCase was verified already and check was true.
    *
    * @param l     The lemma used to attempt to verify the useCase.
    * @param check If check is false, it will not be checked if the useCase was already verified.
    * @return True, if the useCase could be verified.
    */
  private def verifyUseCase(l: Lemma, check: Boolean): Boolean = {
    require(!check || !isUseCaseVerified(), "use case already verified")
    if (TactixLibrary.proveBy(useCaseProofGoal(), by(l)).isProved) {
      useCaseLemma = Some(l)
      true
    }
    else {
      useCaseLemma = None
      false
    }
  }

  /**
    * Tries to verify the step with the provided lemma.
    * Fails if the step was verified already.
    *
    * @param l The lemma used to attempt to verify the step.
    * @return True, if the step could be verified.
    */
  def verifyStep(l: Lemma): Boolean = verifyStep(l, true)

  /**
    * Tries to verify the step with the provided lemma.
    * The lemma is stored in the contract, if successfull.
    * Only fails if the step was verified already and check was true.
    *
    * @param l     The lemma used to attempt to verify the step.
    * @param check If check is false, it will not be checked if the step was already verified.
    * @return True, if the step could be verified.
    */
  private def verifyStep(l: Lemma, check: Boolean): Boolean = {
    require(!check || !isStepVerified(), "step already verified")
    if (TactixLibrary.proveBy(stepProofGoal(), by(l)).isProved) {
      stepLemma = Some(l)
      true
    }
    else {
      stepLemma = None
      false
    }
  }

  /**
    * Loads the given lemma and calls [[verifyBaseCase()]] with the resulting lemma.
    *
    * @param id The ID of the lemma used to verify the baseCase.
    * @return True, if the baseCase could be verified using the lemma.
    *         False, if not or if the lemma was not found.
    */
  def verifyBaseCase(id: LemmaID): Boolean = {
    loadLemma(id) match {
      case Some(l: Lemma) => verifyBaseCase(l)
      case _ => false
    }
  }

  /**
    * Loads the given lemma and calls [[verifyUseCase()]] with the resulting lemma.
    *
    * @param id The ID of the lemma used to verify the useCase.
    * @return True, if the useCase could be verified using the lemma.
    *         False, if not or if the lemma was not found.
    */
  def verifyUseCase(id: LemmaID): Boolean = {
    loadLemma(id) match {
      case Some(l: Lemma) => verifyUseCase(l)
      case _ => false
    }
  }

  /**
    * Loads the given lemma and calls [[verifyStep()]] with the resulting lemma.
    *
    * @param id The ID of the lemma used to verify the step.
    * @return True, if the step could be verified using the lemma.
    *         False, if not or if the lemma was not found.
    */
  def verifyStep(id: LemmaID): Boolean = {
    loadLemma(id) match {
      case Some(l: Lemma) => verifyStep(l)
      case _ => false
    }
  }

  /**
    * Postfix for the name of the lemma used to verify the baseCase
    */
  val BC_NAME: String = "-BaseCase"
  /**
    * Postfix for the name of the lemma used to verify the useCase
    */
  val UC_NAME: String = "-UseCase"
  /**
    * Postfix for the name of the lemma used to verify the step
    */
  val S_NAME: String = "-Step"

  /**
    * Tries to verify the baseCase with the given Tactic.
    * If successful, a lemma is created from the Tactic and [[verifyBaseCase()]] is called with it.
    *
    * @param t The Tactic used to verify the baseCase.
    * @return [[Some]] lemma that was created if the verification of the baseCase was successful,
    *         or [[None]] otherwise.
    */
  def verifyBaseCase(t: BelleExpr): Option[Lemma] = {
    val x = verify(baseCaseProofGoal(), t, Some(component.name + BC_NAME))
    x match {
      case Some(l) => verifyBaseCase(l)
      case _ =>
    }
    x
  }

  /**
    * Tries to verify the useCase with the given Tactic.
    * If successful, a lemma is created from the Tactic and [[verifyUseCase()]] is called with it.
    *
    * @param t The Tactic used to verify the baseCase.
    * @return [[Some]] lemma that was created if the verification of the useCase was successful,
    *         or [[None]] otherwise.
    */
  def verifyUseCase(t: BelleExpr): Option[Lemma] = {
    val x = verify(useCaseProofGoal(), t, Some(component.name + UC_NAME))
    x match {
      case Some(l) => verifyUseCase(l)
      case _ =>
    }
    x
  }

  /**
    * Tries to verify the step with the given Tactic.
    * If successful, a lemma is created from the Tactic and [[verifyStep()]] is called with it.
    *
    * @param t The Tactic used to verify the baseCase.
    * @return [[Some]] lemma that was created if the verification of the step was successful,
    *         or [[None]] otherwise.
    */
  def verifyStep(t: BelleExpr): Option[Lemma] = {
    val x = verify(stepProofGoal(), t, Some(component.name + S_NAME))
    x match {
      case Some(l) => verifyStep(l)
      case _ =>
    }
    x
  }

  /**
    * Creates the actual contract of the component interface pair as [[Formula]].
    *
    * @return The contract.
    */
  def contract(): Formula

  /**
    * Checks if all proof goals (i.e., baseCase, useCase and step) are verified.
    *
    * @return True, if the contract is verified.
    */
  def isVerified() = isBaseCaseVerified() && isUseCaseVerified() && isStepVerified()

  /**
    * Creates the side condition as used in Theorem 1.
    * For the sake of the implementation, the side condition is split into one formula
    * per output variable.
    *
    * @return A [[LinkedHashMap]] with one side condition for each output variable
    */
  def sideConditions(): LinkedHashMap[Variable, Formula]

  /**
    * Creates the compatibility proof obligations for all connected ports
    * between this contract and ctr2, according to X
    *
    * @param ctr2 The second contract (i.e., component), composed with the current one.
    * @param X    The port mapping.
    * @return A map, where each connected port tuple is assigned a compatibility proof obligation.
    */
  def cpo(ctr2: Contract, X: mutable.Map[Variable, Variable]): mutable.Map[(Variable, Variable), Formula]

  /**
    * Returns the current contracts precondition, depending on the type of contract.
    *
    * @return A [[Formula]] representing the precondition.
    */
  def contractPre(): Formula

  /**
    * Returns the current contracts plant, depending on the type of contract.
    *
    * @return An [[ODESystem]] representing the plant.
    */
  def contractPlant(): ODESystem = {
    contractPlant(component.plant)
  }

  /**
    * Returns the contract plant, depending on the type of contract, but using the given plant.
    *
    * @param thePlant The basic plant.
    * @return A [[Formula]] representing the plant.
    */
  def contractPlant(thePlant: ODESystem): ODESystem

  /**
    * Returns the evolution domain, depending on the type of contract, but using the given plant.
    *
    * @return A [[Formula]] representing the evolution domain of the contracts DE.
    */
  def contractDomain(): Formula = contractDomain(component.plant.constraint)


  /**
    * Returns the evolution domain, depending on the type of contract, but using the given plant.
    *
    * @param theConst The basic constraint.
    * @return A [[Formula]] representing the evolution domain of the contracts DE.
    */
  def contractDomain(theConst: Formula): Formula

  /**
    * Returns the current contracts postcondition, depending on the type of contract.
    *
    * @return A [[Formula]] representing the postcondition.
    */
  def contractPost(): Formula

  def variables(): Set[Variable] = {
    component.variables() ++ interface.variables()
  }
}

/**
  * A serializable version of [[Contract]] that can be used to save and load oontracts.
  *
  * @param ctr The contract that should be serialized.
  */
private class SerializableContract(ctr: Contract@transient) extends Serializable {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val _component: SerializableComponent = new SerializableComponent(ctr.component)
  val _interface: SerializableInterface = new SerializableInterface(ctr.interface)
  val _pre: String = ctr.pre.prettyString
  val _post: String = ctr.post.prettyString
  val _invariant: String = ctr.invariant.prettyString
  val _baseCaseLemma: String =
    ctr.baseCaseLemma match {
      case Some(l: Lemma) => l.name match {
        case Some(n) => n
        case _ => null
      }
      case _ => null
    }
  val _useCaseLemma: String =
    ctr.useCaseLemma match {
      case Some(l: Lemma) => l.name match {
        case Some(n) => n
        case _ => null
      }
      case _ => null
    }
  val _stepLemma: String =
    ctr.stepLemma match {
      case Some(l: Lemma) => l.name match {
        case Some(n) => n
        case _ => null
      }
      case _ => null
    }
  val _type: Class[_ <: Contract] = ctr.getClass
  val _verified: Boolean = ctr.isVerified()

  def contract(): Contract = {
    val ret = _type.getConstructors()(0).newInstance(
      _component.component(),
      _interface.interface(),
      _pre.asFormula,
      _post.asFormula,
      _invariant.asFormula,
      loadLemma(_baseCaseLemma),
      loadLemma(_useCaseLemma),
      loadLemma(_stepLemma)).asInstanceOf[Contract]

    if (_verified != ret.isVerified()) throw new Exception("Could not re-verify loaded contract that was saved as verified")

    return ret
  }
}

/**
  * DelayContract according to my thesis.
  *
  * @param component     The component.
  * @param interface     The interface.
  * @param pre           The contracts precondition.
  * @param post          The contracts postcondition.
  * @param invariant     The invariant used to verify the contract.
  * @param baseCaseLemma The lemma used to verify the baseCase. Can be [[None]].
  * @param useCaseLemma  The lemma used to verify the useCase. Can be [[None]].
  * @param stepLemma     The lemma used to verify the step. Can be [[None]].
  */
class DelayContract(component: Component, interface: Interface, pre: Formula, post: Formula, invariant: Formula, baseCaseLemma: Option[Lemma] = None, useCaseLemma: Option[Lemma] = None, stepLemma: Option[Lemma] = None)
  extends Contract(component, interface, pre, post, invariant, baseCaseLemma, useCaseLemma, stepLemma) {

  override def contractPlant(thePlant: ODESystem): ODESystem =
    ODESystem(DifferentialProduct(Globals.plantT, thePlant.ode), contractDomain(thePlant.constraint))

  override def contractDomain(theConst: Formula) = And(theConst, Globals.consT)

  override def contract(): Formula = Imply(
    contractPre(),
    Box(Loop(
      Compose(Compose(Compose(Compose(Compose(interface.deltaPart, component.ctrl), Globals.oldT), contractPlant()), interface.in), component.ports)), contractPost())
  )

  override def contractPost(): Formula = {
    And(post, interface.piOutAll)
  }

  override def proofGoals(): IndexedSeq[Sequent] = _proofGoals

  /**
    * Lazily extracts the proof goals that need to be closed in order to verify the delay contract.
    */
  lazy val _proofGoals: IndexedSeq[Sequent] = {
    val t: BelleExpr = implyR('R) & loop(invariant)('R) < ( //& andL('L) *@ TheType()
      (andLi *) & cut(contractPre()) <
        (hideL(-1) & implyRi partial, hideR(1) & QE) partial, //& print("Base case")
      (andLi *) & cut(invariant) <
        (hideL(-1) & implyRi partial, hideR(1) & QE) partial, //& print("Use Case")
      (andLi *) & cut(invariant) <
        (hideL(-1) & implyRi partial, hideR(1) & QE) partial //& print("Step")
      )
    val p = proveBy(contract(), t)
    p.subgoals
  }

  //
  //  override def tactic(): BelleExpr = {
  //    require(isVerified(), "cannot create tactic for unverified contract")
  //    implyR('R) & loop(invariant)('R) < (
  //      (Contract.preTactic & TactixLibrary.by(baseCaseLemma.get)),
  //      (Contract.preTactic & TactixLibrary.by(useCaseLemma.get)),
  //      (Contract.preTactic & TactixLibrary.by(stepLemma.get))
  //      )
  //  }

  override def sideConditions(): LinkedHashMap[Variable, Formula] = {
    var ret: LinkedHashMap[Variable, Formula] = LinkedHashMap.empty
    ret = this.interface.piOut.map((e) => (e._1,
      Imply(
        this.invariant,
        Box(
          this.interface.deltaPart,
          Box(this.component.ctrl,
            Box(Globals.oldT,
              Box(this.contractPlant(), e._2)
            )
          )
        )
      ).asInstanceOf[Formula]
      )

    )
    ret
  }

  override def cpo(ctr2: Contract, X: mutable.Map[Variable, Variable]): mutable.Map[(Variable, Variable), Formula] = {
    //useless and just to avoid errors
    val ctr1 = this
    var s = mutable.Map.empty[(Variable, Variable), Formula]

    require(X.keySet.subsetOf(ctr1.interface.vIn.toSet ++ ctr2.interface.vIn.toSet) || !X.values.toSet.subsetOf(ctr1.interface.vOut.toSet ++ ctr2.interface.vOut.toSet),
      "invalid port mapping X")
    s ++= X.filter { case (in, out) => ctr1.interface.vIn.contains(in) }.map { case (in, out) => {
      val pre = {
        if (ctr1.interface.pre.keySet.contains(in)) {
          //Delta port, thus initial values must match
          Globals.appendGlobalPropertyToFormula(Equal(ctr1.interface.pre(in), ctr2.interface.pre(out)))
        }
        else {
          //NO delta port
          Globals.globalProp
        }
      }
      ((in, out) -> Imply(pre, Box(Assign(in, out), Imply(ctr2.interface.piOut(out), ctr1.interface.piIn(in)))))
    }
    }
    s ++= X.filter { case (in, out) => ctr2.interface.vIn.contains(in) }.map { case (in, out) => {
      val pre = {
        if (ctr1.interface.pre.keySet.contains(in)) {
          //Delta port, thus initial values must match
          Globals.appendGlobalPropertyToFormula(Equal(ctr2.interface.pre(in), ctr1.interface.pre(out)))
        }
        else {
          //NO delta port
          Globals.globalProp
        }
      }
      (in, out) -> Imply(pre, Box(Assign(in, out), Imply(ctr1.interface.piOut(out), ctr2.interface.piIn(in))))
    }
    }
    return s
  }

  override def contractPre(): Formula = Globals.appendGlobalPropertyToFormula(And(Globals.initT, pre))
}

/**
  * Helper functions used in contracts.
  */
object Contract {

  /**
    * Creates the side condition F used in the proof of Theorem1 (for delay contracts!)
    * for composing the two components, using the given mapping.
    *
    * @param ctr1 The first contract (i.e., component) to be composed.
    * @param ctr2 The second contract (i.e., component) to be composed.
    * @param X    The port mapping.
    * @return A [[Seq]] containing two [[Formula]] representing the side conditions.
    */
  def sideConditionsProofDelay(ctr1: Contract, ctr2: Contract, X: mutable.LinkedHashMap[Variable, Variable]): Seq[Formula] = {
    Seq(
      Imply(
        ctr1.invariant,
        Box(
          Interface.compose(ctr1.interface, ctr2.interface, X).deltaPart,
          Box(Compose(ctr2.component.ctrl, ctr1.component.ctrl),
            Box(Globals.oldT,
              Box(ctr1.contractPlant(Component.compose(ctr1.component, ctr2.component, Contract.composedPorts(X)).plant), ctr1.interface.piOutAll)
            )
          )
        )
      ),
      Imply(
        ctr2.invariant,
        Box(
          Interface.compose(ctr1.interface, ctr2.interface, X).deltaPart,
          Box(Compose(ctr1.component.ctrl, ctr2.component.ctrl),
            Box(Globals.oldT,
              Box(ctr1.contractPlant(Component.compose(ctr1.component, ctr2.component, Contract.composedPorts(X)).plant), ctr2.interface.piOutAll)
            )
          )
        )
      )

    )
  }


  /**
    * Saves the given contract as [[SerializableContract]] using the given filename.
    *
    * @param ctr   The contract to be saved.
    * @param fName The target filename.
    */
  def save(ctr: Contract, fName: String) = {
    val stream = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    stream.writeObject(new SerializableContract(ctr))
    stream.close()
  }

  /**
    * Loads the contract from the given filename.
    *
    * @param fName The source filename.
    * @return The loaded contract.
    */
  def load(fName: String): Contract = {
    val stream = new ObjectInputStream(new FileInputStream(new File(fName)))
    val ret = stream.readObject().asInstanceOf[SerializableContract].contract()
    stream.close()
    return ret
  }

  /**
    * Check if the interface is admissible for the component.
    *
    * @param component The component.
    * @param interface The interface.
    * @return True, if the interface is admissible for the component.
    */
  def admissible(component: Component, interface: Interface): Boolean = {
    bv(component.ctrl).intersect(interface.vDelta).isEmpty &&
      (bv(component.ctrl) ++ bv(component.plant) ++ bv(component.ports)).intersect(interface.vInit).isEmpty &&
      (bv(component.ctrl) ++ bv(component.plant)).intersect(interface.vIn).isEmpty
  }

  /**
    * Create the Change contract for the given parameters.
    * TODO: CHECK BEFORE USE!
    *
    * @param component The component.
    * @param interface The interface.
    * @param pre       The precondition.
    * @param post      The postcondition.
    * @return The change contract.
    */
  def changeContract(component: Component, interface: Interface, pre: Formula, post: Formula): Formula = {
    Imply(
      Globals.appendGlobalPropertyToFormula(pre),
      Box(Loop(
        Compose(Compose(Compose(Compose(interface.deltaPart, component.ctrl), component.plant), interface.in), component.ports)), post)
    )
  }

  /**
    * Extracts the proof goals that need to be closed in order to verify the change contract.
    * TODO: MOVE TO CLASS CHANGECONTRACT UPON CREATION!
    *
    * @param component The component.
    * @param interface The admissible interface.
    * @param pre       The initial condition.
    * @param post      The safety property.
    * @param inv       The loop invariant used.
    * @return Three proof goals: base case, use case, step.
    */
  def changeProofGoals(component: Component, interface: Interface, pre: Formula, post: Formula, inv: Formula): IndexedSeq[Sequent] = {
    val preTactic = (andLi *) & implyRi
    val t: BelleExpr = implyR('R) & loop(inv)('R) < ( //& andL('L) *@ TheType()
      preTactic partial, //& print("Base case")
      preTactic partial, //& print("Use Case")
      preTactic partial //& print("Step")
      )
    val p = proveBy(changeContract(component, interface, pre, post), t)
    p.subgoals
  }

  def composeWithLemmas[C <: Contract](ctr1: C, ctr2: C, X: mutable.LinkedHashMap[Variable, Variable], cpoT: mutable.Map[(Variable, Variable), Lemma], side1T: mutable.Map[Variable, Lemma], side2T: mutable.Map[Variable, Lemma], verify: Boolean = true): C = {
    compose(ctr1, ctr2, X, cpoT.map { case (k, v) => k -> v.fact }, side1T.map { case (k, v) => k -> v.fact }, side2T.map { case (k, v) => k -> v.fact }, verify)
  }

  //TODO untested!
  def composeWithSideTactics[C <: Contract](ctr1: C, ctr2: C, X: mutable.LinkedHashMap[Variable, Variable], cpoT: mutable.Map[(Variable, Variable), BelleExpr], side1T: mutable.Map[Variable, BelleExpr], side2T: mutable.Map[Variable, BelleExpr]): C = {
    val side1 = side1T.map((e) => (e._1, TactixLibrary.proveBy(ctr1.sideConditions()(e._1), e._2)))
    val side2 = side2T.map((e) => (e._1, TactixLibrary.proveBy(ctr2.sideConditions()(e._1), e._2)))
    val cpo = cpoT.map((e) => (e._1, TactixLibrary.proveBy((ctr1.cpo(ctr2, X) ++ ctr2.cpo(ctr1, X)) (e._1), e._2)))
    require(side1.forall((e) => e._2.isProved), "sideT1 must proof all side condition of ctr1")
    require(side2.forall((e) => e._2.isProved), "sideT2 must proof all side condition of ctr2")
    require(cpo.forall((e) => e._2.isProved), "cpoT must proof all compatibility proof obligations")
    compose(ctr1, ctr2, X, cpo, side1, side2)
  }

  /**
    * Composes two contracts with port mapping X.
    * The composite component is then verified utilizing the provided tactics/provables
    * for verifying the compatibility proof obligations and the side conditions for
    * both components.
    *
    * @param ctr1  The first contract.
    * @param ctr2  The second contract.
    * @param X     The port mapping.
    * @param cpoT  The tactics to verify the compatibility proof obligations.
    * @param side1 A provable verifying the side condition for the first component.
    * @param side2 A provable verifying the side condition for the second component.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The verified composit contract.
    */
  def compose[C <: Contract](ctr1: C, ctr2: C, X: mutable.LinkedHashMap[Variable, Variable], cpoT: mutable.Map[(Variable, Variable), Provable], side1: mutable.Map[Variable, Provable], side2: mutable.Map[Variable, Provable], verify: Boolean = true): C = {
    //Initial checks
    require(ctr1.getClass.equals(ctr2.getClass), "only contracts of the same type can be composed")
    require(!verify || (ctr1.isVerified() && ctr2.isVerified()), "only verified contracts can be composed and verified")

    //Compose all parts of the contract
    val ports: Program = composedPorts(X)
    val i3 = Interface.compose(ctr1.interface, ctr2.interface, X)
    val c3 = Component.compose(ctr1.component, ctr2.component, ports)
    val pre3 = composedPre(ctr1, ctr2, X)
    val post3 = composedPost(ctr1, ctr2)
    val inv3 = composedInvariant(ctr1, ctr2, X)

    //Construct a new contract
    val constructor = ctr1.getClass.getConstructors()(0)
    val ctr3 = constructor.newInstance(c3, i3, pre3, post3, inv3, None, None, None).asInstanceOf[C]

    if (!verify) return ctr3

    //Automatically verify new contract, following theorem from my thesis
    // Verify CPO

    // Verify side condition

    // Verify composite contract
    // move andLs???
    //- how to handle the global property? outermost formula?
    //    ctr3.verifyBaseCase(implyR('R) & andR('R) < (andR('R) < (
    //      //... |- inv1
    //      andL('L) & andL('L) & hideL(-3) & andL('L) & hideL(-3) & andLi *@ TheType() & implyRi & by(ctr1.baseCaseLemma.get)
    //      ,
    //      //... |- inv2
    //    andL('L) & andL('L) & hideL(-3) & andL('L) & hideL(-2) & andLi *@ TheType() & implyRi & by(ctr2.baseCaseLemma.get)
    //      ),
    //      //... |- composedBootstrap
    //      andL('L) & andL('L) & hideL(-2) & hideL(-1) & andLi *@ TheType() & close(-1, 1) //implyRi & by(ctr2.baseCaseLemma.get)
    //      )
    //    )

    //    val outTactic = {
    //      if (ctr1.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).nonEmpty) {
    //        if (ctr2.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).nonEmpty) {
    //          println("both have out ports!")
    //          (andR('R) < (
    //            //... |- out1
    //            hideL(-3) & hideL(-1) & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
    //              //use cut
    //              prop,
    //              //show cut
    //              hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
    //              )
    //            ,
    //            //... |- out2
    //            hideL(-2) & hideL(-1) & cut(ctr2.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
    //              //use cut
    //              prop,
    //              //show cut
    //              hideR(1) & implyRi & by(ctr2.useCaseLemma.get)
    //              )
    //            )
    //            )
    //        }
    //        else {
    //          println("only c1 has out ports!")
    //          //... |- out1
    //          hideL(-3) & hideL(-1) & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
    //            //use cut
    //            prop,
    //            //show cut
    //            hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
    //            )
    //        }
    //      }
    //      else {
    //        if (ctr2.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).nonEmpty) {
    //          println("only c2 has out ports!")
    //          //... |- out2
    //          hideL(-2) & hideL(-1) & cut(ctr2.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
    //            //use cut
    //            prop,
    //            //show cut
    //            hideR(1) & implyRi & by(ctr2.useCaseLemma.get)
    //            )
    //        }
    //        else {
    //          println("none has out ports!")
    //          prop
    //        }
    //      }
    //    }
    //    ctr3.verifyUseCase(implyR('R) & andL('L) & andL('L) & andR('R) < (andR('R) < (
    //      //... |- post1
    //      hideL(-3) & hideL(-1) & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
    //        //use cut
    //        prop,
    //        //show cut
    //        hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
    //        )
    //      ,
    //      //... |- post2
    //      hideL(-2) & hideL(-1) & cut(ctr2.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
    //        //use cut
    //        prop
    //          & print("use") partial,
    //        //show cut
    //        hideR(1) & implyRi & by(ctr2.useCaseLemma.get)
    //          & print("show") partial
    //        ) partial
    //      ), outTactic
    //      )
    //    )

    val nIn1: Int = if (ctr1.interface.in.isInstanceOf[Compose]) ComposeProofStuff.countBinary[Compose](ctr1.interface.in.asInstanceOf[Compose]) else 0
    val nPorts1: Int = if (ctr1.component.ports.isInstanceOf[Compose]) ComposeProofStuff.countBinary[Compose](ctr1.component.ports.asInstanceOf[Compose]) else 0

    ctr3.verifyStep(implyR('R)
      //
      & boxAnd('R) & andR('R) < (
      boxAnd('R) & andR('R) < (
        boxAnd('R) & andR('R) < (
          //inv1 - partial
          print("inv1")
            & composeb('R) * 5 & choiceb(1, List(1)) & boxAnd('R) & andR('R) < (
            //inv1-C1;C2 - DONE
            print("C1;C2")
              //cf. 1 - cut F2out
              & cut(sideConditionsProofDelay(ctr1, ctr2, X)(1)) < (
              //use cut
              andL('L) & andL('L) & andL('L) & implyL(-1) // -1 global, -2 bootstrap, -3 inv1, -4 inv2
                < (
                //the left side of implyL closes immediately, since we know inv2 holds
                close(-4, 2)
                ,
                //cf. 3 - drop ports2
                useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 4 & composeb(1, 1 :: Nil) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))(1) & Lemmas.lemma1AB('R)
                  //cf. 4 - drop in2
                  //TODO test this stuff with multiple ports in in1 and in2
                  & composeb(1) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))('L) * 3
                  & ComposeProofStuff.dropIn(ctr2.interface.vIn)('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in1*][ports1][ports3]inv1
                  //cf. 5-9 - introduce, move and weaken test, weaken assignment
                  //  first split all parts of in1 from the rest
                  & composeb('R) * (ctr1.interface.piOut.filter((e) => !X.values.toSet.contains(e._1)).size)
                  //  and merge all parts of in1
                  & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) * (ctr1.interface.piOut.filter((e) => !X.values.toSet.contains(e._1)).size / 2)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][in1*][ports1][ports3]inv1
                  //  introduce tests, move them, weaken them, make assignment non-deterministic and move both to designated position
                  & ComposeProofStuff.introduceAndWeakenForAll(ctr1.interface.piIn, ctr2.interface.piOut, X, cpoT)('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][in1][ports1][ports3*]inv1
                  //cf. 3 - drop remaining parts of ports3 (which are part of component 2)
                  & ComposeProofStuff.dropRemainingPorts3(ctr2.interface.vIn)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][in1][ports1]inv1
                  //cf. 11 - drop plant2
                  & composeb(1) & Lemmas.lemma2_DC(mutable.Seq(ctr2.variables().toSeq: _*), ctr2.component.plant.constraint)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;plant1][in1][ports1]inv1
                  //cf. 13 - drop ctr2
                  & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: 1 :: Nil)
                  //cf. 13 - drop dp2
                  & (
                  if (ctr2.interface.vDelta.isEmpty) {
                    //empty dp2, nothing to remove
                    skip
                  }
                  else {
                    //there is something in dp2, so remove it
                    if (ctr1.interface.vDelta.isEmpty) {
                      //empty dp1, so drop dp3 and introduce ?true;
                      //TODO UNTESTED!
                      Lemmas.lemma1(1, 0 :: Nil) & Lemmas.lemma5T("true".asFormula) < (skip, closeT)
                    }
                    else {
                      //there is something in dp1 too, so we have to check what to remove
                      //TODO MISSING!
                      skip
                    }
                  }
                  )
                  //CLOSE - cut lemma formula and close branches
                  & cut(ctr1.stepLemma.get.fact.conclusion.succ(0)) < (
                  hide(-1) * 3 & hide(-2) & modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & hide(-1)
                    //Splitting ante: [dp1;ctrl1;told;plant1;in1;ports1]inv1
                    //split ports1 and split further
                    & composeb(-1) & (composeb(-1, 1 :: Nil) * nPorts1)
                    //split in1 and split further
                    & composeb(-1) & ((composeb(-1, 1 :: Nil) & composeb(-1, 1 :: 1 :: Nil)) * Math.max((nIn1 + 1) / 2 - 1, 0))
                    & (if (nIn1 > 0) composeb(-1, 1 :: Nil) else skip)
                    //split plant1, told, ctrl1, dp1
                    & composeb(-1) * 3
                    //close
                    & closeId,
                  cohide(2) & implyR('R) & useAt(ctr1.stepLemma.get, PosInExpr(1 :: Nil))(1) & prop
                  )
                )
              ,
              //show cut - DONE
              //(1) remove all but the show-cut part
              hideAllButLastSucc()
                //(2) --> r
                & implyR('R)
                //vaphi2 ==> [dp][ctrl1;ctrl2][told][{plant1,plant2}]piout2
                //(3) cf. 1 - Lemma 2 to remove plant1
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 2 & Lemmas.lemma2_DC(mutable.Seq(ctr1.variables().toSeq: _*), ctr1.component.plant.constraint)('R)
                //vaphi2 ==> [dp;ctrl1;ctrl2;told][{plant2}]piout2
                //(4) cf. 2 - Lemma 1 to remove ctrl1
                & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1AB('R)
                //vaphi2 ==> [dp][ctrl2][told][{plant2}]piout2
                //(5) cf. 2 - Lemma 1 to remove dp1
                & ComposeProofStuff.removeDeltaParts(ctr1.interface.vDelta.size, true)('R)
                //vaphi2 ==> [dp][ctrl2][told][{plant2}]piout2
                //(6) cf. 3 - close all branches with sideconditions for each part of piout2
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 3 & (
                if (ctr2.interface.piOut.size == 0) closeT
                else (boxAnd('R) & andR('R)
                  < (skip, ComposeProofStuff.closeSide(side2)('R) & prop)) * (ctr2.interface.piOut.size - 1) & ComposeProofStuff.closeSide(side2)('R) & prop
                ) //closed!
              )
            ,
            //inv1-C1;C2 - TODO
            print("C2;C1 - TODO") partial
            ) partial
          ,
          //inv2 - TODO
          print("inv2 - TODO") partial
          ) partial,
        //pre boot - DONE
        //TODO does this master() always close, or should I try to reduce the thing further? (how??)
        hideL(-1) & composeb('R) & G('R) & master() //& print("boot closed?")
        ) partial,
      //global - DONE
      V('R) & prop //& print("global closed?")
      )
      & print("todo") partial
    )

    //Return verified composite contract
    return ctr3
  }

  object ComposeProofStuff {
    def dropRemainingPorts3(vs: Seq[Variable]): DependentPositionTactic = "Drop Remaining Ports3" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, b: Box)) =>
        var t: BelleExpr = skip
        vs.foreach(v => {
          t = t & dropFromPorts3(v)(pos)
        })
        t
    })

    def dropFromPorts3(v: Variable): DependentPositionTactic = "Drop From Ports3" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, b: Box)) =>
        var t: BelleExpr = skip
        val assPos = posOfAssign(b, v)
        if (assPos > 0) {
          //the assignment was found
          t = t & Lemmas.lemma1(1, oneList(assPos))
        }
        t
    })

    def dropIn(vIn: Seq[Variable]): DependentPositionTactic = "Drop Input Ports" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(_, Box(in3: Compose, _))) =>
        var n = countBinary[Compose](in3.asInstanceOf[Compose])
        var t: BelleExpr = skip
        if (n > 1) {
          n = n / 2
          t = t & composeb(pos.top.getPos, 1 :: Nil) * n
          t = t & (dropOrMerge(vIn)(pos.top.getPos) * (n + 1))
        }
        else {
          t = t & (dropOrMerge(vIn)(pos.top.getPos) * n)
        }
        t
      //TODO test the case with the test!
      case Some(Box(_, Box(in3: Test, _))) => Lemmas.lemma1AB(pos.top.getPos)
    })

    def dropOrMerge(vIn: Seq[Variable]): DependentPositionTactic = "Drop Or Merge" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(_, Box(b, _))) =>
        if (v(b).intersect(vIn).nonEmpty) {
          Lemmas.lemma1AB(pos.top.getPos)
        }
        else {
          useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos)
        }
    })

    def closeSide(side: mutable.Map[Variable, Provable]): DependentPositionTactic = "Close With Sidecondition" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(Compose(Compose(Compose(dp, ctrl), told), plant), out)) =>
        composeb('R) * 3 & useAt(side(side.keySet.intersect(v(out).toSet).toSeq(0)), PosInExpr(1 :: Nil))('R) & closeId
    })

    def introduceAndWeakenForAll(piIn: LinkedHashMap[Variable, Formula], piOut: LinkedHashMap[Variable, Formula], X: mutable.LinkedHashMap[Variable, Variable], cpoT: mutable.Map[(Variable, Variable), Provable]): DependentPositionTactic = "Introduce Tests For All" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, Box(in1, Box(ports1, Box(ports3, _))))) =>
        var t: BelleExpr = skip
        val vtIn: mutable.LinkedHashMap[Variable, Formula] = piIn.filter((e) => X.keySet.contains(e._1))
        val vtOut: mutable.LinkedHashMap[Variable, Formula] = piOut.filter((e) => X.values.toSet.contains(e._1))

        //[p][in1][ports1][ports3]A
        var nPorts3 = if (ports3.isInstanceOf[Compose]) {
          //multiple assignments --> compose
          (countBinary[Compose](ports3.asInstanceOf[Compose]) + 1)
        }
        else if (ports3.isInstanceOf[Assign]) {
          //single assignment
          1
        }
        else {
          //no assignment, but empty test
          0
        }
        var hPorts3 = 1 :: 1 :: 1 :: Nil
        if (nPorts3 > 1) {
          (0 until nPorts3 - 1) foreach (i => {
            t = t & print("goPorts3") & composeb(pos.top.getPos, hPorts3) & print("wentPorts3")
          })
        }

        //[p][in1][ports1][ports3-1]...[ports3-nPorts3]A
        val nPorts1 = if (ports1.isInstanceOf[Compose]) {
          //multiple assignments --> compose
          (countBinary[Compose](ports1.asInstanceOf[Compose]) + 1)
        }
        else if (ports1.isInstanceOf[Assign]) {
          //single assignment
          1
        }
        else {
          //no assignment, but empty test
          0
        }
        var hPorts1 = 1 :: 1 :: Nil
        if (nPorts1 > 1) {
          (0 until nPorts1 - 1) foreach (i => {
            t = t & print("goPorts1") & composeb(pos.top.getPos, hPorts1) & print("wentPorts1")
            //            hPorts1 = 1 :: hPorts1
          })
        }

        //[p][in1][ports1-1]...[ports1-nPorts1][ports3-1]...[ports3-nPorts3]A
        var hIn1 = 1 :: Nil
        var nIn1 = 0
        if (in1.isInstanceOf[Compose]) {
          //in1 is not empty
          nIn1 = (countBinary[Compose](in1.asInstanceOf[Compose]) + 1) / 2
          // compose in1 into pieces. for each port there is a randomb and a test. so we have n-1 compose statements. each pair is decomposed and then split.
          (0 until nIn1 - 1) foreach (i => {
            t = t & (print("go") & composeb(pos.top.getPos, hIn1)) * 2
            hIn1 = 1 :: 1 :: hIn1
          })
          t = t & print("go last") & composeb(pos.top.getPos, hIn1) & print("go done")
        }

        //[p][random-in1-1][test-in1-1]...[random-in1-nIn1][test-in1-nIn1][ports1-1]...[ports1-nPorts1][ports3-1]...[ports3-nPorts3]A
        var donePorts = Seq.empty[Variable]
        vtIn.foreach((e) => {
          val inPos = piIn.keys.toSeq.indexOf(e._1)
          val portPos = X.keys.toSeq.diff(donePorts).indexOf(e._1)
          t = t & ComposeProofStuff.introduceTestFor(e._1, e._2, X.get(e._1).get, vtOut.get(X.get(e._1).get).get, nIn1, nPorts1, nPorts3, inPos, portPos, cpoT((e._1, X(e._1))))(pos)
          donePorts = donePorts ++ Seq(e._1)
          nIn1 = nIn1 + 1
          nPorts3 = nPorts3 - 1
        })
        t
    })


    def introduceTestFor(vIn: Variable, tIn: Formula, vOut: Variable, tOut: Formula, nIn1: Int, nPorts1: Int, nPorts3: Int, inPos: Int, portPos: Int, cpo: Provable): DependentPositionTactic = "Introduce Test For" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, _)) =>
        //Initially we have:
        //[p][random-in1-1][test-in1-1]...[random-in1-nIn1][test-in1-nIn1][ports1-1]...[ports1-nPorts1][ports3-1]...[ports3-nPorts3]A
        val cntIn1 = if (nIn1 == 0) 1 else nIn1 * 2
        val cntPorts1 = if (nPorts1 == 0) 1 else nPorts1
        val cntPorts3 = if (nPorts3 == 0) 1 else nPorts3

        var h = 1 :: 1 :: Nil
        //introduce test using lemma 5
        var t: BelleExpr = print("start introduceTestFor") & Lemmas.lemma5T(tOut)(pos) < (skip, hide(-2) * 4 & implyRi & CMon(PosInExpr(1 :: Nil)) & prop)
        //split test from p to get: [p][test][in1...][ports1...][ports3...]A
        t = t & composeb(pos)
        //commute test through in3
        t = t & print("commute through in3")

        h = 1 :: Nil
        (0 until nIn1) foreach (i => {
          t = t & print("a") & Lemmas.lemma4_4T(pos.top.getPos, h)
          h = 1 :: h
          t = t & print("b") & Lemmas.lemma4_6T(pos.top.getPos, h) & print("c")
          h = 1 :: h
        })
        t = t & print("done with in3")

        //commute test with ports1
        //TODO WE ASSUME THAT PORTS1 IS ALWAYS ?TRUE --> if we want to use composition of composites, this is NOT the case! --> so far only atomic components can be composed
        require(nPorts1 == 0, "so far only atomic components can be composed")
        t = t & print("commute through ports1") & Lemmas.lemma4_6T(pos.top.getPos, oneList(1 + cntIn1))
        t = t & print("done with ports1")

        //locate v in ports1 and move test there
        t = t & print("commute to position in ports1")
        val assPos = posOfAssign(seq.sub(pos).get.asInstanceOf[Box], vIn)
        println("assPos: " + assPos)
        h = oneList(1 + cntIn1 + cntPorts1)
        (1 + cntIn1 + cntPorts1 until assPos) foreach (i => {
          t = t & Lemmas.lemma4_5T(pos.top.getPos, h)
          h = 1 :: h
        })
        t = t & print("done moving to position in ports1")

        //weaken test
        t = t & print("weakening test")
        t = t & Lemmas.lemma6T(tIn)(pos.top.getPos, h) < (
          //hier gehts weiter!
          skip
          ,
          (useAt("[;] compose", PosInExpr(1 :: Nil))('R) *) & composeb('R)
            & useAt(cpo, PosInExpr(1 :: Nil))(1, 1 :: Nil)
            //[dp3;(ctrl1;ctrl2);told;plant3;in1;ports1;ports3*]A
            //remove all remaining parts of ports3*, and all of ports1 and in1, and plant3, told and (ctrl1;ctr2).
            & ((composeb('R) & Lemmas.lemma1AB(1)) * (assPos + 1))
            //next, apply all assignments in dp3
            & (((composeb('R) | skip) & (assignb('R) | (testb('R) & useAt(DerivedAxioms.trueImplies, PosInExpr(0 :: Nil))('R)))) *)
            //now QE should close the thing
            //TODO DOES IT?
            & hide(-1) & QE
          //            & print("cutting, cpo=" + cpo) & cutAt(cpo.conclusion.succ.head.asInstanceOf[Imply].left)(1, 1 :: Nil)
          //            //TODO HERE WE ARE...how to apply this lemma 6 and solve this?
          //            < (skip, print("hiding") & cohide(2) & V('R) & print("hide and imply") & useAt(cpo, PosInExpr(1 :: Nil))('R) & closeId)
          //            //            & cut(cpo.conclusion.succ.head) < (skip, ProofHelper.hideAllButLastSucc & implyR('R) & useAt(cpo, PosInExpr(1 :: Nil))('R) & closeId)
          ) & print("done weakening")

        //[p][in1...][ports1...][ports3*...]A
        //make assignment non-deterministic
        t = t & print("make non-det")
        t = t & useAt(Lemmas.lemma3, PosInExpr(1 :: Nil))(1, oneList(assPos - 1))
        t = t & print("done making non-det")

        //[p][in1...][ports1...][ports3*...]A
        //rotate new non-det assignment to designated position
        t = t & print("commute new non-det port to designated position")
        //  1) commute non-det assign with remaining ports3
        (cntIn1 + cntPorts1 + portPos).until(cntIn1 + cntPorts1, -1) foreach (i => {
          t = t & Lemmas.lemma4_1T(1, oneList(i))
        })
        //  2) commute non-det assign with ports1
        //  TODO WE ASSUME THAT PORTS1 IS ALWAYS ?TRUE --> if we want to use composition of composites, this is NOT the case! --> so far only atomic components can be composed
        t = t & Lemmas.lemma4_4T(1, oneList(cntIn1 + cntPorts1))
        //  3) commute non-det assign with in1
        if (nIn1 == 0) {
          //its just a test
          t = t & Lemmas.lemma4_4T(1, oneList(cntIn1 + cntPorts1))
        }
        else {
          //there are actual open ports
          (cntIn1).until(inPos * 2, -2) foreach (i => {
            t = t & Lemmas.lemma4_4T(1, oneList(i)) & Lemmas.lemma4_2T(1, oneList(i - 1))
          })
        }
        //rotate test to designated position
        t = t & print("commute test to designated position")
        //  1) commute test with remaining ports3
        (cntIn1 + cntPorts1 + portPos + 1).until(cntIn1 + cntPorts1 + 1, -1) foreach (i => {
          t = t & Lemmas.lemma4_5T(1, oneList(i))
        })
        //  2) commute test with ports1
        //  TODO WE ASSUME THAT PORTS1 IS ALWAYS ?TRUE --> if we want to use composition of composites, this is NOT the case! --> so far only atomic components can be composed
        t = t & Lemmas.lemma4_6T(1, oneList(cntIn1 + cntPorts1 + 1))
        //  3) commute test with in1
        if (nIn1 == 0) {
          //its just a test
          t = t & Lemmas.lemma4_6T(1, oneList(cntIn1 + cntPorts1 + 1))
        }
        else {
          //there are actual open ports
          (cntIn1 + 1).until(inPos * 2 + 1, -2) foreach (i => {
            t = t & Lemmas.lemma4_6T(1, oneList(i)) & Lemmas.lemma4_4T(1, oneList(i - 1))
          })
        }
        t = t & print("done commuting non-det assignment and test")


        t
    })

    def posOfAssign(b: Box, v: Variable): Int = {
      b match {
        case Box(Assign(a, _), f) if a.equals(v) => 1
        case Box(x, b2: Box) => posOfAssign(b2, v) + 1
        case _ => Int.MinValue
      }
    }

    def oneList(c: Int): List[Int] = {
      var l: List[Int] = Nil
      (0 until c) foreach (i => l = (1 :: l))
      l
    }

    def removeDeltaParts(cnt: Int, left: Boolean): DependentPositionTactic = "Remove DeltaParts" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(dp, f: Formula)) =>
        var t: BelleExpr = skip //print("removeDP!")
        //        println("compose # " + countCompose(dp.asInstanceOf[Compose]))
        if (dp.isInstanceOf[Test]) {
          //          println("[removeDeltaParts]: Just a test, so nothing to do here.")
        }
        else if (dp.isInstanceOf[Assign]) {
          //          println("[removeDeltaParts]: Just a single assignment...")
          if (cnt == 1) {
            t = t & Lemmas.lemma1BA(pos)
            t = t & introduceEmptyTest(pos, seq, f)
          }
        }
        else {
          val nr = countBinary[Compose](dp.asInstanceOf[Compose])
          //          println("[removeDeltaParts]: Multiple (nr=" + (nr + 1) + ") assignments...")
          if (cnt == 0) {
            //            println("[removeDeltaParts]: Nothing to do, since cnt=" + cnt + "...")
          }
          else {
            if (cnt == nr + 1) {
              t = t & Lemmas.lemma1BA(pos.top.getPos)
              t = t & introduceEmptyTest(pos, seq, f)
            }
            else {
              val newCnt = if (!left)
                nr + 1 - cnt
              else
                cnt
              var s: List[Int] = Nil
              (0 until newCnt) foreach (i => {
                t = t & composeb(pos.top.getPos, s)
                if (left) t = t & Lemmas.lemma1BA(pos.top)
                else s = List(1) ++ s
              })
              if (!left) {
                (0 until newCnt - 1) foreach (i => {
                  t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos)
                })
                if (newCnt != 0) t = t & Lemmas.lemma1AB(pos.top.getPos)
                else t = t & Lemmas.lemma1BA(pos.top.getPos)
              }
            }
          }
        }
        //        t = t & print("done!")
        t
    })

    def introduceEmptyTest(pos: Position, seq: Sequent, f: Formula): BelleExpr = cut(Box(Test("true".asFormula), f)) < (
      //use cut
      testb(seq.ante.size - 1) & implyL(seq.ante.size - 1) < (close, closeId)
      ,
      //show cut
      hide(pos.top)
      )

    def countBinary[C <: BinaryComposite](c: C): Integer = c match {
      case Compose(c1: C, c2: C) => countBinary(c1) + countBinary(c2) + 1
      case Compose(c1: C, _) => countBinary(c1) + 1
      case Compose(_, c2: C) => countBinary(c2) + 1
      case Compose(_, _) => 1
    }
  }

  def main(args: Array[String]): Unit = {
    ProofHelper.initProver
    //    TactixLibrary.proveBy("[a:=a1;b:=b1;c:=c1;d:=d1;]true".asFormula, ComposeProofStuff.removeDeltaParts(0, false)('R) & print("a"))
    TactixLibrary.proveBy("[a:=a1;b:=b1;]b>0".asFormula, print("a") & ComposeProofStuff.removeDeltaParts(0, false)('R))
    ProofHelper.shutdownProver
  }

  /**
    * Create the ports part for the composit contract.
    *
    * @param X The port mapping.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The ports part of the composit.
    */
  def composedPorts[C <: Contract](X: mutable.LinkedHashMap[Variable, Variable]): Program = {
    X.map(x => Assign(x._1, x._2).asInstanceOf[Program]) match {
      case ass if ass.nonEmpty => ass.reduce((a1, a2) => Compose(a1, a2))
      case _ => Test(True)
    }
  }

  /**
    * Create the invariant for the composit contract.
    *
    * @param ctr1 The first contract.
    * @param ctr2 The second contract.
    * @param X    The port mapping.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The invariant of the composit.
    */
  private def composedInvariant[C <: Contract](ctr1: C, ctr2: C, X: mutable.Map[Variable, Variable]): And = {
    Globals.appendGlobalPropertyToFormula(And(And(ctr1.invariant, ctr2.invariant), composedBootstrap(X)))
  }

  /**
    * Create the postcondition for the composit contract.
    *
    * @param ctr1 The first contract.
    * @param ctr2 The second contract.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The postcondition of the composit.
    */
  private def composedPost[C <: Contract](ctr1: C, ctr2: C): And = {
    And(ctr1.post, ctr2.post)
  }

  /**
    * Create the precondition for the composit contract.
    *
    * @param ctr1 The first contract.
    * @param ctr2 The second contract.
    * @param X    The port mapping.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The precondition of the composit.
    */
  private def composedPre[C <: Contract](ctr1: C, ctr2: C, X: mutable.Map[Variable, Variable]): And = {
    And(And(ctr1.pre, ctr2.pre), composedBootstrap(X))
  }

  /**
    * Create the bootstrapping part for the composit contract.
    * i.e., X(v) = v , for all v in the mapping
    *
    * @param X The port mapping.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The bootstrapping of the composit.
    */
  private def composedBootstrap[C <: Contract](X: mutable.Map[Variable, Variable]): BinaryComposite with Formula with Product with Serializable = {
    X.map { case (in, out) => Equal(in, out) }.reduce((a: Formula, b: Formula) => And(a, b))
  }
}
