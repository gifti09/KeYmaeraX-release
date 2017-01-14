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

  def tactic(bcl: Lemma, ucl: Lemma, sl: Lemma): BelleExpr = implyR('R) & loop(invariant)('R) < ( //& andL('L) *@ TheType()
    (andLi *) & cut(contractPre()) <
      (hideL(-1) & implyRi & by(bcl), hideR(1) & QE), //& print("Base case")
    (andLi *) & cut(invariant) <
      (hideL(-1) & implyRi & by(ucl), hideR(1) & QE), //& print("Use Case")
    (andLi *) & cut(invariant) <
      (hideL(-1) & implyRi & by(sl), hideR(1) & QE) //& print("Step")
  )

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
  def sideConditions(): LinkedHashMap[Seq[Variable], Formula]

  /**
    * Creates the compatibility proof obligations for all connected ports
    * between this contract and ctr2, according to X
    *
    * @param ctr2 The second contract (i.e., component), composed with the current one.
    * @param X    The port mapping.
    * @return A map, where each connected port tuple is assigned a compatibility proof obligation.
    */
  def cpo(ctr2: Contract, X: mutable.Map[Seq[Variable], Seq[Variable]]): mutable.Map[(Seq[Variable], Seq[Variable]), Formula]

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
  def contractDomain(): Formula = if (component.plant == null) True else contractDomain(component.plant.constraint)


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
    if (thePlant == null)
      ODESystem(Globals.plantT, contractDomain(null))
    else
      ODESystem(DifferentialProduct(Globals.plantT, thePlant.ode), contractDomain(if (thePlant == null) null else thePlant.constraint))

  override def contractDomain(theConst: Formula) = if (theConst == null) And(True, Globals.evoDomT) else And(theConst, Globals.evoDomT)

  override def contract(): Formula = Imply(
    contractPre(),
    Box(Loop(
      Compose(
        Compose(
          Compose(
            Compose(
              Compose(
                interface.deltaPart, component.ctrl
              ), Globals.oldT
            ), contractPlant()
          ), interface.in
        ), component.ports
      )
    ), contractPost())
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

  override def sideConditions(): LinkedHashMap[Seq[Variable], Formula] = {
    var ret: LinkedHashMap[Seq[Variable], Formula] = LinkedHashMap.empty
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

  override def cpo(ctr2: Contract, X: mutable.Map[Seq[Variable], Seq[Variable]]): mutable.Map[(Seq[Variable], Seq[Variable]), Formula] = {
    //useless and just to avoid errors
    val ctr1 = this
    var s = mutable.Map.empty[(Seq[Variable], Seq[Variable]), Formula]

    require(X.keySet.subsetOf(ctr1.interface.vIn.toSet ++ ctr2.interface.vIn.toSet)
      || !X.values.toSet.subsetOf(ctr1.interface.vOut.toSet ++ ctr2.interface.vOut.toSet),
      "invalid port mapping X")
    s ++= X.filter { case (in, out) => ctr1.interface.vIn.contains(in) }.map { case (in, out) => {
      val pre = {
        if (ctr1.interface.pre.keySet.contains(in)) {
          //Delta port, thus initial values must match
          //          Globals.appendGlobalPropertyToFormula(Equal(ctr1.interface.pre(in), ctr2.interface.pre(out)))
          Globals.appendGlobalPropertyToFormula(MultiPort.equals(ctr1.interface.pre(in), ctr2.interface.pre(out)))
        }
        else {
          //NO delta port
          Globals.globalProp
        }
      }
      ((in, out) -> Imply(pre, Box(MultiPort.assign(in, out), Imply(ctr2.interface.piOut(out), ctr1.interface.piIn(in)))))
    }
    }
    s ++= X.filter { case (in, out) => ctr2.interface.vIn.contains(in) }.map { case (in, out) => {
      val pre = {
        if (ctr2.interface.pre.keySet.contains(in)) {
          //Delta port, thus initial values must match
          Globals.appendGlobalPropertyToFormula(MultiPort.equals(ctr2.interface.pre(in), ctr1.interface.pre(out)))
        }
        else {
          //NO delta port
          Globals.globalProp
        }
      }
      (in, out) -> Imply(pre, Box(MultiPort.assign(in, out), Imply(ctr1.interface.piOut(out), ctr2.interface.piIn(in))))
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
  val PRINT_BC = false
  val PRINT_UC = false
  val PRINT_STEP = false
  val PRINT_RECOMPOSE_DP = PRINT_STEP
  val PRINT_DROP_DELTA_PARTS = PRINT_STEP
  val PRINT_DROP_DELTA_PART_FOR_PORT = PRINT_STEP
  val PRINT_DROP_OR_SKIP_DELTA_PART = PRINT_STEP
  val PRINT_DROP_REMAINING_PORTS3 = PRINT_STEP
  val PRINT_DROP_FROM_PORTS3 = PRINT_STEP
  val PRINT_DROP_IN = PRINT_STEP | true
  val PRINT_DROP_OR_MERGE = PRINT_STEP
  val PRINT_CLOSE_SIDE = PRINT_STEP
  val PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL = PRINT_STEP
  val PRINT_INTRODUCE_AND_WEAKEN_FOR = PRINT_STEP

  /**
    * Creates the side condition F used in the proof of Theorem1 (for delay contracts!)
    * for composing the two components, using the given mapping.
    *
    * @param ctr1 The first contract (i.e., component) to be composed.
    * @param ctr2 The second contract (i.e., component) to be composed.
    * @param X    The port mapping.
    * @return A [[Seq]] containing two [[Formula]] representing the side conditions.
    */
  def sideConditionsProofDelay(ctr1: Contract, ctr2: Contract, X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]]): Seq[Formula] = {
    Seq(
      Imply(
        ctr2.invariant,
        Box(
          Interface.compose(ctr1.interface, ctr2.interface, X).deltaPart,
          Box(Compose(ctr2.component.ctrl, ctr1.component.ctrl),
            Box(Globals.oldT,
              Box(ctr1.contractPlant(Component.compose(ctr1.component, ctr2.component, Contract.composedPorts(X)).plant), ctr2.interface.piOutAll)
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
      ),
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
        ctr1.invariant,
        Box(
          Interface.compose(ctr1.interface, ctr2.interface, X).deltaPart,
          Box(Compose(ctr1.component.ctrl, ctr2.component.ctrl),
            Box(Globals.oldT,
              Box(ctr1.contractPlant(Component.compose(ctr1.component, ctr2.component, Contract.composedPorts(X)).plant), ctr1.interface.piOutAll)
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
    //    bv(component.ctrl).intersect(interface.vDeltaFlat).isEmpty &&
    (bv(component.ctrl) ++ bv(component.plant) ++ bv(component.ports)).intersect(interface.vInitFlat).isEmpty &&
      (bv(component.ctrl) ++ bv(component.plant)).intersect(interface.vInFlat).isEmpty
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

  def composeWithLemmas[C <: Contract](ctr1: C, ctr2: C, X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]], cpoT: mutable.Map[(Seq[Variable], Seq[Variable]), Lemma], side1T: mutable.Map[Seq[Variable], Lemma], side2T: mutable.Map[Seq[Variable], Lemma], verify: Boolean = true): C = {
    compose(ctr1, ctr2, X,
      if (cpoT == null) null else cpoT.map { case (k, v) => k -> v.fact },
      if (side1T == null) null else side1T.map { case (k, v) => k -> v.fact },
      if (side2T == null) null else side2T.map { case (k, v) => k -> v.fact },
      verify)
  }

  //TODO untested!
  def composeWithSideTactics[C <: Contract](ctr1: C, ctr2: C, X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]], cpoT: mutable.Map[(Seq[Variable], Seq[Variable]), BelleExpr], side1T: mutable.Map[Seq[Variable], BelleExpr], side2T: mutable.Map[Seq[Variable], BelleExpr]): C = {
    val side1 = side1T.map((e) => (e._1, TactixLibrary.proveBy(ctr1.sideConditions()(e._1), e._2)))
    val side2 = side2T.map((e) => (e._1, TactixLibrary.proveBy(ctr2.sideConditions()(e._1), e._2)))
    val cpo = cpoT.map((e) => (e._1, TactixLibrary.proveBy((ctr1.cpo(ctr2, X) ++ ctr2.cpo(ctr1, X)) (e._1), e._2)))
    require(side1.forall((e) => e._2.isProved), "sideT1 must proof all side condition of ctr1")
    require(side2.forall((e) => e._2.isProved), "sideT2 must proof all side condition of ctr2")
    require(cpo.forall((e) => e._2.isProved), "cpoT must proof all compatibility proof obligations")
    compose(ctr1, ctr2, X, cpo, side1, side2)
  }


  //HACK FOR ROBIX? -> 0-no, 1-yes
  var hack: Int = 0

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
  def compose[C <: Contract](ctr1: C, ctr2: C, X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]], cpoT: mutable.Map[(Seq[Variable], Seq[Variable]), Provable], side1: mutable.Map[Seq[Variable], Provable], side2: mutable.Map[Seq[Variable], Provable], verify: Boolean = true, check: Boolean = false): C = {
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

    if (check) {
      // Verify CPO
      require(ctr1.cpo(ctr2, X).forall { case ((vi: Seq[Variable], vo: Seq[Variable]), f: Formula) => {
        TactixLibrary.proveBy(f, byUS(cpoT(vi, vo))).isProved
      }
      }, "cpoT must proof cpo")

      // Verify side condition
      require(ctr1.sideConditions().forall { case (vs: Seq[Variable], f: Formula) => {
        TactixLibrary.proveBy(f, byUS(side1(vs))).isProved
      }
      }, "side1 must proof sideconditions of ctr1")
      require(ctr2.sideConditions().forall { case (vs: Seq[Variable], f: Formula) => {
        TactixLibrary.proveBy(f, byUS(side2(vs))).isProved
      }
      }, "side2 must proof sideconditions of ctr2")
    }


    //Automatically verify composite contract, following theorem from my thesis using CPO, side conditions and component proofs
    ctr3.verifyBaseCase(
      implyR('R) & andR('R) < (andR('R) < (andR('R) < (
        //... |- inv1
        (if (PRINT_BC) print("BC-inv1") else skip) &
          andL('L) * 3 & hide(-4) & andL(-3) & hideL(-4) &
          andLi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(-3).asInstanceOf[AntePos]) &
          andLi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(-1).asInstanceOf[AntePos]) &
          implyRi & by(ctr1.baseCaseLemma.get)
        ,
        //... |- inv2
        (if (PRINT_BC) print("BC-inv2") else skip) &
          andL('L) * 3 & hide(-4) & andL(-3) & hideL(-3) &
          andLi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(-3).asInstanceOf[AntePos]) &
          andLi(SeqPos(-2).asInstanceOf[AntePos], SeqPos(-1).asInstanceOf[AntePos]) &
          implyRi & by(ctr2.baseCaseLemma.get)
      ),
        //... |- composedBootstrap
        (if (PRINT_BC) print("BC-bootstrap") else skip) &
          andL('L) * 3 & hide(-1) * 3 & close(-1, 1)
      ),
        //... |- globalProperty
        (if (PRINT_BC) print("BC-global") else skip) &
          andL('L) * 3 & hide(-2) * 3 & close(-1, 1)
      )
        & (if (PRINT_BC) print("BC-done?") else skip)
    )

    //Tactic for the output-port conditions of useCase
    var outTactic = skip
    if (ctr1.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).nonEmpty) {
      if (ctr2.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).nonEmpty) {
        outTactic = (if (PRINT_UC) print("UC-outTactic: both have out ports!") else skip)
        (0 until ctr2.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).size) foreach (i => {
          outTactic = outTactic & andR('R) < (
            //remaining ports
            skip,
            //handle next port of out2
            hideL(-1) * 3 & cut(ctr2.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
              //use cut
              prop,
              //show cut
              hideR(1) & implyRi & by(ctr2.useCaseLemma.get)
            )
          )
        })

        (0 until ctr1.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).size - 1) foreach (i => {
          outTactic = outTactic & andR('R) < (
            //remaining ports
            skip,
            //handle next port of out1
            hideL(-4) & hideL(-1) * 2 & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
              //use cut
              prop,
              //show cut
              hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
            )
          )
        })
        //handle last port of out1
        outTactic = outTactic & hideL(-4) & hideL(-1) * 2 & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
          //use cut
          prop,
          //show cut
          hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
        )
      }
      else {
        //... |- out1
        outTactic = (if (PRINT_UC) print("UC-outTactic: only c1 has out ports!") else skip) & hideL(-4) & hideL(-1) * 2 & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
          //use cut
          prop,
          //show cut
          hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
        )
      }
    }
    else {
      if (ctr2.interface.piOut.keySet.intersect(ctr3.interface.piOut.keySet).nonEmpty) {
        //... |- out2
        outTactic = (if (PRINT_UC) print("UC-outTactic: only c2 has out ports!") else skip) & hideL(-1) * 3 & cut(ctr2.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
          //use cut
          prop,
          //show cut
          hideR(1) & implyRi & by(ctr2.useCaseLemma.get)
        )
      }
      else {
        outTactic = (if (PRINT_UC) print("UC-outTactic: none has out ports!") else skip) & prop
      }
    }

    ctr3.verifyUseCase((if (PRINT_UC) print("UC: usecase") else skip) & implyR('R) & andL('L) * 3 & andR('R) < (andR('R) < (
      //... |- post1
      hideL(-4) & hideL(-1) * 2 & cut(ctr1.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
        //use cut
        prop,
        //show cut
        hideR(1) & implyRi & by(ctr1.useCaseLemma.get)
      )
      ,
      //... |- post2
      hideL(-1) * 3 & cut(ctr2.useCaseLemma.get.fact.conclusion.succ(0).asInstanceOf[Imply].right) < (
        //use cut
        prop,
        //show cut
        hideR(1) & implyRi & by(ctr2.useCaseLemma.get)
      )
    ),
      // ...|- out
      outTactic
    )
      & (if (PRINT_UC) print("UC: done?") else skip)
    )

    //    return null.asInstanceOf[C]

    //    val nIn1: Int = if (ctr1.interface.in.isInstanceOf[Compose]) ComposeProofStuff.countBinary[Compose](ctr1.interface.in.asInstanceOf[Compose]) else 0
    val nPorts1: Int = if (ctr1.component.ports.isInstanceOf[Compose]) ComposeProofStuff.countBinary[Compose](ctr1.component.ports.asInstanceOf[Compose]) else 0
    //    val nIn2: Int = if (ctr2.interface.in.isInstanceOf[Compose]) ComposeProofStuff.countBinary[Compose](ctr2.interface.in.asInstanceOf[Compose]) else 0
    val nPorts2: Int = if (ctr2.component.ports.isInstanceOf[Compose]) ComposeProofStuff.countBinary[Compose](ctr2.component.ports.asInstanceOf[Compose]) else 0

    ctr3.verifyStep(implyR('R)
      //
      & boxAnd('R) & andR('R) < (
      boxAnd('R) & andR('R) < (
        boxAnd('R) & andR('R) < (
          //inv1 - DONE
          (if (PRINT_STEP) print("inv1") else skip)
            & composeb('R) * 5 & choiceb(1, List(1)) & boxAnd('R) & andR('R) < (
            //inv1-C1;C2 - DONE
            (if (PRINT_STEP) print("inv1-C1;C2") else skip)
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
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in1*;in2*;ports1][ports3]inv1
                  //cf. 4 - drop in2
                  & composeb(1) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))('L) * 3
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in1*;in2*][ports1][ports3]inv1
                  //TODO check
                  & ComposeProofStuff.dropIn(mutable.Seq((ctr2.interface.vIn.toSet -- X.keySet).toSeq: _*), mutable.Seq(ctr3.interface.vIn: _*))('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in1*][ports1][ports3]inv1
                  //cf. 5-9 - introduce, move and weaken test, weaken assignment
                  //  first split all parts (i.e., all the [...=*; ?...;]) of in1 from the rest
                  //TODO Check
                  & composeb('R) * (Math.max((ctr1.interface.vIn.toSet -- X.keySet).size, 1))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}[?in1*;in1*:=*]...[?in1*;in1*:=*][ports1][ports3]inv1
                  //  and merge all parts of in1
                  //TODO Check
                  & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) * (Math.max((ctr1.interface.vIn.toSet -- X.keySet).size - 1, 0))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][?in1*;in1*:=*;?in1*;in1*:=*][ports1][ports3]inv1
                  //  introduce tests, move them, weaken them, make assignment non-deterministic and move both to designated position
                  & ComposeProofStuff.introduceAndWeakenForAll(ctr1.interface.piIn, ctr2.interface.piOut, X, cpoT, ctr3.interface.vIn)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][?in1][in1:=*]...[?in1][in1:=*][ports1][ports3*]...[ports3*]inv1
                  //cf. 3 - drop remaining parts of ports3 (which are part of component 2)
                  //TODO Check
                  & ComposeProofStuff.dropRemainingPorts3(ctr2.interface.vIn, X)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  //cf. 11 - drop plant2
                  & composeb(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told][[plant1,plant2}][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  & print("HACK ONE-1")
                  & Lemmas.lemma2_DC(mutable.Seq(ctr2.variables().toSeq: _*), if (ctr2.component.plant == null) null else ctr2.component.plant.constraint, 2 * hack)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;plant1][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  //cf. 13 - drop ctr2
                  & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: 1 :: Nil)
                  //F,global,boot,inv1,inv2 ==> [dp1;dp2][ctrl1][told][plant1][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  //cf. 13 - drop dp2
                  & ComposeProofStuff.dropDeltaParts(ctr2.interface.vDelta.isEmpty, ctr1.interface.vDelta.isEmpty, ctr2.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                  //CLOSE - cut lemma formula and close branches
                  & cut(ctr1.stepLemma.get.fact.conclusion.succ(0)) < (
                  hide(-1) * 3 & hide(-2) & modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & hide(-1)
                    //Splitting ante: [dp1;ctrl1;told;plant1;in1;ports1]inv1
                    //split ports1 and split further
                    & composeb(-1) & (composeb(-1, 1 :: Nil) * nPorts1)
                    //split in1 and split further
                    & composeb(-1) & ((composeb(-1, 1 :: Nil) & (composeb(-1, 1 :: 1 :: Nil) *)) * Math.max(ctr1.interface.vIn.size - 1, 0))
                    & (if (ctr1.interface.vIn.size > 0) (composeb(-1, 1 :: Nil) *) else skip)
                    //split plant1, told, ctrl1, dp1
                    & composeb(-1) * 3
                    //split dp1
                    & (composeb(-1) & (composeb(-1, 1 :: Nil) *)) * Math.max(ctr1.interface.pre.size - 1, 0)
                    & (if (ctr1.interface.pre.size > 0) (composeb(-1) *) else skip)
                    //close
                    & closeId,
                  cohide(2) & implyR('R) & useAt("ANON", ctr1.stepLemma.get.fact, PosInExpr(1 :: Nil))(1) & prop
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
                & print("HACK ONE-2")
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 2 & Lemmas.lemma2_DC(mutable.Seq(ctr1.variables().toSeq: _*), if (ctr1.component.plant == null) null else ctr1.component.plant.constraint, 1 * hack)('R)
                //vaphi2 ==> [dp;ctrl1;ctrl2;told][{plant2}]piout2
                //(4) cf. 2 - Lemma 1 to remove ctrl1
                & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1AB('R)
                //vaphi2 ==> [dp2][ctrl2][told][{plant2}]piout2
                //(5) cf. 2 - Lemma 1 to remove dp1
                //                & ComposeProofStuff.removeDeltaParts(ctr1.interface.vDelta.size, true)('R)
                //TODO check
                & ComposeProofStuff.dropDeltaParts(ctr1.interface.vDelta.isEmpty, ctr2.interface.vDelta.isEmpty, ctr1.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                //vaphi2 ==> [dp2][ctrl2][told][{plant2}]piout2
                //(6) cf. 3 - close all branches with sideconditions for each part of piout2
                //  first reconnect DP
                & ComposeProofStuff.recomposeDP(ctr2.interface.vDelta)('R)
                // then reconnect to one big box
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * (3)
                & (
                if (ctr2.interface.piOut.size == 0) cohide(1) & boxTrue(1)
                else (boxAnd('R) & andR('R)
                  < (skip, ComposeProofStuff.closeSide(side2)('R) & prop)) * (ctr2.interface.piOut.size - 1)
                  & ComposeProofStuff.closeSide(side2)('R) & prop
                ) //closed!
            ) & (if (PRINT_STEP) print("C1;C2 done!") else skip)
            ,
            //inv1-C2;C1 - DONE
            (if (PRINT_STEP) print("inv1-C2;C1") else skip)
              //cf. 1 - cut F2out
              & cut(sideConditionsProofDelay(ctr1, ctr2, X)(0)) < (
              //use cut
              andL('L) & andL('L) & andL('L) & implyL(-1) // -1 global, -2 bootstrap, -3 inv1, -4 inv2
                < (
                //the left side of implyL closes immediately, since we know inv2 holds
                close(-4, 2)
                ,
                //cf. 3 - drop ports2
                useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 4 & composeb(1, 1 :: Nil) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))(1) & Lemmas.lemma1AB('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2};in1*;in2*;ports1][ports3]inv1                  //cf. 4 - drop in2
                  & composeb(1) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))('L) * 3
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2};in1*;in2*][ports1][ports3]inv1
                  //TODO check
                  & ComposeProofStuff.dropIn(mutable.Seq((ctr2.interface.vIn.toSet -- X.keySet).toSeq: _*), mutable.Seq(ctr3.interface.vIn: _*))('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2};in1*][ports1][ports3]inv1
                  //cf. 5-9 - introduce, move and weaken test, weaken assignment
                  //  first split all parts of in1 from the rest
                  //                  & composeb('R) * (ctr1.interface.piOut.filter((e) => !X.values.toSet.contains(e._1)).size)
                  & composeb('R) * (Math.max((ctr1.interface.vIn.toSet -- X.keySet).size, 1))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}[?in1*;in1*:=*]...[?in1*;in1*:=*][ports1][ports3]inv1
                  //  and merge all parts of in1
                  & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) * (Math.max((ctr1.interface.vIn.toSet -- X.keySet).size - 1, 0))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}][?in1*;in1*:=*;?in1*;in1*:=*][ports1][ports3]inv1
                  //  introduce tests, move them, weaken them, make assignment non-deterministic and move both to designated position
                  & ComposeProofStuff.introduceAndWeakenForAll(ctr1.interface.piIn, ctr2.interface.piOut, X, cpoT, ctr3.interface.vIn)('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}][?in1][in1:=*]...[?in1][in1:=*][ports1][ports3*]...[ports3*]inv1
                  //cf. 3 - drop remaining parts of ports3 (which are part of component 2)
                  & ComposeProofStuff.dropRemainingPorts3(ctr2.interface.vIn, X)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  //cf. 11 - drop plant2
                  & composeb(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told][[plant1,plant2}][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  & print("HACK TWO-1")
                  & Lemmas.lemma2_DC(mutable.Seq(ctr2.variables().toSeq: _*), if (ctr2.component.plant == null) null else ctr2.component.plant.constraint, 2 * hack)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;plant1][?in1][in1:=*]...[?in1][in1:=*][ports1]inv1
                  //cf. 13 - drop ctr2
                  & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: Nil)
                  //cf. 13 - drop dp2
                  & ComposeProofStuff.dropDeltaParts(ctr2.interface.vDelta.isEmpty, ctr1.interface.vDelta.isEmpty, ctr2.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                  //CLOSE - cut lemma formula and close branches
                  & cut(ctr1.stepLemma.get.fact.conclusion.succ(0)) < (
                  hide(-1) * 3 & hide(-2) & modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & hide(-1)
                    //Splitting ante: [dp1;ctrl1;told;plant1;in1;ports1]inv1
                    //split ports1 and split further
                    & composeb(-1) & (composeb(-1, 1 :: Nil) * nPorts1)
                    //split in1 and split further
                    & composeb(-1) & ((composeb(-1, 1 :: Nil) & (composeb(-1, 1 :: 1 :: Nil) *)) * Math.max(ctr1.interface.vIn.size - 1, 0))
                    & (if (ctr1.interface.vIn.size > 0) (composeb(-1, 1 :: Nil) *) else skip)
                    //split plant1, told, ctrl1, dp1
                    & composeb(-1) * 3
                    //split dp1
                    & (composeb(-1) & (composeb(-1, 1 :: Nil) *)) * Math.max(ctr1.interface.pre.size - 1, 0)
                    & (if (ctr1.interface.pre.size > 0) (composeb(-1) *) else skip)
                    //                    & composeb(-1) * (ctr1.interface.pre.size - 1)
                    //close
                    & closeId,
                  cohide(2) & implyR('R) & useAt("ANON", ctr1.stepLemma.get.fact, PosInExpr(1 :: Nil))(1) & prop
                )
              )
              ,
              //show cut - DONE
              //(1) remove all but the show-cut part
              hideAllButLastSucc()
                //(2) --> r
                & implyR('R)
                //vaphi2 ==> [dp][ctrl2;ctrl1][told][{plant1,plant2}]piout2
                //(3) cf. 1 - Lemma 2 to remove plant1
                & print("HACK TWO-2")
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 2 & Lemmas.lemma2_DC(mutable.Seq(ctr1.variables().toSeq: _*), if (ctr1.component.plant == null) null else ctr1.component.plant.constraint, 1 * hack)('R)
                //vaphi2 ==> [dp;ctrl1;ctrl2;told][{plant2}]piout2
                //(4) cf. 2 - Lemma 1 to remove ctrl1
                & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: 1 :: Nil)
                //vaphi2 ==> [dp][ctrl2][told][{plant2}]piout2
                //(5) cf. 2 - Lemma 1 to remove dp1
                //TODO check
                & ComposeProofStuff.dropDeltaParts(ctr1.interface.vDelta.isEmpty, ctr2.interface.vDelta.isEmpty, ctr1.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                //vaphi2 ==> [dp][ctrl2][told][{plant2}]piout2
                //(6) cf. 3 - close all branches with sideconditions for each part of piout2
                //  first reconnect DP
                & ComposeProofStuff.recomposeDP(ctr2.interface.vDelta)('R)
                // then reconnect to one big box
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * (3)
                & (
                if (ctr2.interface.piOut.size == 0) cohide(1) & boxTrue(1)
                else (boxAnd('R) & andR('R)
                  < (skip, ComposeProofStuff.closeSide(side2)('R) & prop)) * (ctr2.interface.piOut.size - 1) & ComposeProofStuff.closeSide(side2)('R) & prop
                ) //closed!
            ) & (if (PRINT_STEP) print("C2;C1 done!") else skip)
          )
          ,
          //inv2 - DONE
          (if (PRINT_STEP) print("inv2 ") else skip)
            & composeb('R) * 5 & choiceb(1, List(1)) & boxAnd('R) & andR('R) < (
            //inv2-C1;C2 - DONE
            (if (PRINT_STEP) print("inv2-C1;C2") else skip)
              //cf. 1 - cut F1out
              & cut(sideConditionsProofDelay(ctr1, ctr2, X)(3)) < (
              //use cut
              andL('L) & andL('L) & andL('L) & implyL(-1) // -1 global, -2 bootstrap, -3 inv1, -4 inv2
                < (
                //the left side of implyL closes immediately, since we know inv1 holds
                close(-3, 2)
                ,
                //cf. 3 - drop ports1
                useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 4 & composeb(1, 1 :: Nil) * 2 & Lemmas.lemma1(1, 1 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in1*;in2*;ports2][ports3]inv2
                  //cf. 4 - drop in1
                  & composeb(1) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))('L) * 3
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in1*;in2*][ports2][ports3]inv2
                  //TODO Check
                  & ComposeProofStuff.dropIn(mutable.Seq((ctr1.interface.vIn.toSet -- X.keySet).toSeq: _*), mutable.Seq(ctr3.interface.vIn: _*))('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in2*][ports2][ports3]inv2
                  //cf. 5-9 - introduce, move and weaken test, weaken assignment
                  //  first split all parts (i.e., all the [...=*; ?...;]) of in2 from the rest
                  & composeb('R) * (Math.max((ctr2.interface.vIn.toSet -- X.keySet).size, 1))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}[?in1*;in1*:=*]...[?in1*;in1*:=*][ports1][ports3]inv2
                  //  and merge all parts of in2
                  & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) * (Math.max((ctr2.interface.vIn.toSet -- X.keySet).size - 1, 0))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][?in2*;in2*:=*;?in2*;in2*:=*][ports2][ports3]inv2
                  //  introduce tests, move them, weaken them, make assignment non-deterministic and move both to designated position
                  & ComposeProofStuff.introduceAndWeakenForAll(ctr2.interface.piIn, ctr1.interface.piOut, X, cpoT, ctr3.interface.vIn)('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][?in2][in2:=*]...[?in2][in2:=*][ports2][ports3*]...[ports3*]inv2
                  //cf. 3 - drop remaining parts of ports3 (which are part of component 1)
                  & ComposeProofStuff.dropRemainingPorts3(ctr1.interface.vIn, X)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2}][?in2][in2:=*]...[?in2][in2:=*][ports2]inv2
                  //cf. 11 - drop plant1
                  & composeb(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told][[plant1,plant2}][?in2][in2:=*]...[?in2][in2:=*][ports2]inv2
                  & print("HACK THREE-1")
                  & Lemmas.lemma2_DC(mutable.Seq(ctr1.variables().toSeq: _*), if (ctr1.component.plant == null) null else ctr1.component.plant.constraint, 1 * hack)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;plant1][?in2][in2:=*]...[?in2][in2:=*][ports2]inv2
                  //cf. 13 - drop ctr1
                  & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: Nil)
                  //cf. 13 - drop dp1
                  //TODO check
                  & ComposeProofStuff.dropDeltaParts(ctr1.interface.vDelta.isEmpty, ctr2.interface.vDelta.isEmpty, ctr1.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                  //CLOSE - cut lemma formula and close branches
                  & cut(ctr2.stepLemma.get.fact.conclusion.succ(0)) < (
                  hide(-1) * 4 & modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & hide(-1)
                    //Splitting ante: [dp2;ctrl2;told;plant2;in2;ports2]inv2
                    //split ports2 and split further
                    & composeb(-1) & (composeb(-1, 1 :: Nil) * nPorts2)
                    //split in2 and split further
                    & composeb(-1) & ((composeb(-1, 1 :: Nil) & (composeb(-1, 1 :: 1 :: Nil) *)) * Math.max(ctr2.interface.vIn.size - 1, 0))
                    & (if (ctr2.interface.vIn.size > 0) (composeb(-1, 1 :: Nil) *) else skip)
                    //split plant2, told, ctrl2, dp2
                    & composeb(-1) * 3
                    //split dp2
                    & (composeb(-1) & (composeb(-1, 1 :: Nil) *)) * Math.max(ctr2.interface.pre.size - 1, 0)
                    & (if (ctr2.interface.pre.size > 0) (composeb(-1) *) else skip)
                    //                    & composeb(-1) * (ctr2.interface.pre.size - 1)
                    //close
                    & closeId,
                  cohide(2) & implyR('R) & useAt("ANON", ctr2.stepLemma.get.fact, PosInExpr(1 :: Nil))(1) & prop
                )
              )
              ,
              //show cut - DONE
              //(1) remove all but the show-cut part
              hideAllButLastSucc()
                //(2) --> r
                & implyR('R)
                //vaphi1 ==> [dp][ctrl1;ctrl2][told][{plant1,plant2}]piout1
                //(3) cf. 1 - Lemma 2 to remove plant2
                & print("HACK THREE-2")
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 2 & Lemmas.lemma2_DC(mutable.Seq(ctr2.variables().toSeq: _*), if (ctr2.component.plant == null) null else ctr2.component.plant.constraint, 2 * hack)('R)
                //vaphi1 ==> [dp;ctrl1;ctrl2;told][{plant1}]piout1
                //(4) cf. 2 - Lemma 1 to remove ctrl2
                & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: 1 :: Nil)
                //vaphi1 ==> [dp1;dp2][ctrl1][told][{plant1}]piout1
                //(5) cf. 2 - Lemma 1 to remove dp2
                & ComposeProofStuff.dropDeltaParts(ctr2.interface.vDelta.isEmpty, ctr1.interface.vDelta.isEmpty, ctr2.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                //                & ComposeProofStuff.removeDeltaParts(ctr2.interface.vDelta.size, true)('R)
                //vaphi1 ==> [dp1][ctrl1][told][{plant1}]piout1
                //(6) cf. 3 - close all branches with sideconditions for each part of piout1
                //  first reconnect DP
                & ComposeProofStuff.recomposeDP(ctr1.interface.vDelta)('R)
                // then reconnect to one big box
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * (3)
                & (
                if (ctr1.interface.piOut.size == 0) cohide(1) & boxTrue(1)
                else (boxAnd('R) & andR('R)
                  < (skip, ComposeProofStuff.closeSide(side1)('R) & prop)) * (ctr1.interface.piOut.size - 1)
                  & ComposeProofStuff.closeSide(side1)('R) & prop
                )
              //closed!
            ) & (if (PRINT_STEP) print("C1;C2 done!") else skip)
            ,
            //inv2-C2;C1 - DONE
            (if (PRINT_STEP) print("inv2-C2;C1") else skip)
              //cf. 1 - cut F1out
              & cut(sideConditionsProofDelay(ctr1, ctr2, X)(2)) < (
              //use cut
              andL('L) & andL('L) & andL('L) & implyL(-1) // -1 global, -2 bootstrap, -3 inv1, -4 inv2
                < (
                //the left side of implyL closes immediately, since we know inv1 holds
                close(-3, 2)
                ,
                //cf. 3 - drop ports1
                useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 4 & composeb(1, 1 :: Nil) * 2 & Lemmas.lemma1(1, 1 :: Nil) & useAt("[;] compose", PosInExpr(1 :: Nil))(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2};in1*;in2*;ports2][ports3]inv2
                  //cf. 4 - drop in1
                  & composeb(1) * 2 & useAt("[;] compose", PosInExpr(1 :: Nil))('L) * 3
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2};in1*;in2*][ports2][ports3]inv2
                  & ComposeProofStuff.dropIn(mutable.Seq((ctr1.interface.vIn.toSet -- X.keySet).toSeq: _*), mutable.Seq(ctr3.interface.vIn: _*))('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl1;ctrl2;told;[plant1,plant2};in2*][ports2][ports3]inv2
                  //cf. 5-9 - introduce, move and weaken test, weaken assignment
                  //  first split all parts (i.e., all the [...=*; ?...;]) of in2 from the rest
                  & composeb('R) * (Math.max((ctr2.interface.vIn.toSet -- X.keySet).size, 1))
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}[?in2*;in2*:=*]...[?in2*;in2*:=*][ports2][ports3]inv2
                  //  and merge all parts of in2
                  & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) * (Math.max((ctr2.interface.vIn.toSet -- X.keySet).size - 1, 0))
                  //                  & useAt("[;] compose", PosInExpr(1 :: Nil))(1, 1 :: Nil) * ((ctr2.interface.vIn.toSet -- X.keySet).size / 2)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}][?in2*;in2*:=*;?in2*;in2*:=*][ports2][ports3]inv2
                  //  introduce tests, move them, weaken them, make assignment non-deterministic and move both to designated position
                  & ComposeProofStuff.introduceAndWeakenForAll(ctr2.interface.piIn, ctr1.interface.piOut, X, cpoT, ctr3.interface.vIn)('R)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}][?in2][in2:=*]...[?in2][in2:=*][ports2][ports3*]...[ports3*]inv2
                  //cf. 3 - drop remaining parts of ports3 (which are part of component 1)
                  & ComposeProofStuff.dropRemainingPorts3(ctr1.interface.vIn, X)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;[plant1,plant2}][?in2][in2:=*]...[?in2][in2:=*][ports2]inv2
                  //cf. 11 - drop plant1
                  & composeb(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told][[plant1,plant2}][?in2][in2:=*]...[?in2][in2:=*][ports2]inv2
                  & print("HACK FOUR-1")
                  & Lemmas.lemma2_DC(mutable.Seq(ctr1.variables().toSeq: _*), if (ctr1.component.plant == null) null else ctr1.component.plant.constraint, 1 * hack)(1)
                  //F,global,boot,inv1,inv2 ==> [dp3;ctrl2;ctrl1;told;plant2][?in2][in2:=*]...[?in2][in2:=*][ports2]inv2
                  //cf. 13 - drop ctr1
                  & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: 1 :: Nil)
                  //cf. 13 - drop dp1
                  & ComposeProofStuff.dropDeltaParts(ctr1.interface.vDelta.isEmpty, ctr2.interface.vDelta.isEmpty, ctr1.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                  //CLOSE - cut lemma formula and close branches
                  & cut(ctr2.stepLemma.get.fact.conclusion.succ(0)) < (
                  hide(-1) * 4 & modusPonens(SeqPos(-1).asInstanceOf[AntePos], SeqPos(-2).asInstanceOf[AntePos]) & hide(-1)
                    //Splitting ante: [dp2;ctrl2;told;plant2;in2;ports2]inv2
                    //split ports2 and split further
                    & composeb(-1) & (composeb(-1, 1 :: Nil) * nPorts2)
                    //split in2 and split further
                    & composeb(-1) & ((composeb(-1, 1 :: Nil) & (composeb(-1, 1 :: 1 :: Nil) *)) * Math.max(ctr2.interface.vIn.size - 1, 0))
                    & (if (ctr2.interface.vIn.size > 0) (composeb(-1, 1 :: Nil) *) else skip)
                    //split plant2, told, ctrl2, dp2
                    & composeb(-1) * 3
                    //split dp2
                    & (composeb(-1) & (composeb(-1, 1 :: Nil) *)) * Math.max(ctr2.interface.pre.size - 1, 0)
                    & (if (ctr2.interface.pre.size > 0) (composeb(-1) *) else skip)
                    //                    & composeb(-1) * (ctr2.interface.pre.size - 1)
                    //close
                    & closeId,
                  cohide(2) & implyR('R) & useAt("ANON", ctr2.stepLemma.get.fact, PosInExpr(1 :: Nil))(1) & prop
                )
              )
              ,
              //show cut - DONE
              //(1) remove all but the show-cut part
              hideAllButLastSucc()
                //(2) --> r
                & implyR('R)
                //vaphi1 ==> [dp][ctrl2;ctrl1][told][{plant1,plant2}]piout1
                //(3) cf. 1 - Lemma 2 to remove plant2
                & print("HACK FOUR-2")
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * 2 & Lemmas.lemma2_DC(mutable.Seq(ctr2.variables().toSeq: _*), if (ctr2.component.plant == null) null else ctr2.component.plant.constraint, 2 * hack)('R)
                //vaphi1 ==> [dp;ctrl2;ctrl1;told][{plant1}]piout1
                //(4) cf. 2 - Lemma 1 to remove ctrl2
                & composeb(1) * 2 & composeb(1, 1 :: Nil) & Lemmas.lemma1(1, 1 :: Nil)
                //vaphi1 ==> [dp1;dp2][ctrl1][told][{plant1}]piout1
                //(5) cf. 2 - Lemma 1 to remove dp2
                & ComposeProofStuff.dropDeltaParts(ctr2.interface.vDelta.isEmpty, ctr1.interface.vDelta.isEmpty, ctr2.interface.vInitFlat, ctr3.interface.vDelta.size, ctr3.interface.vDeltaFlat.size)(1)
                //vaphi1 ==> [dp1][ctrl1][told][{plant1}]piout1
                //(6) cf. 3 - close all branches with sideconditions for each part of piout1
                //  first reconnect DP
                & ComposeProofStuff.recomposeDP(ctr1.interface.vDelta)('R)
                // then reconnect to one big box
                & useAt("[;] compose", PosInExpr(1 :: Nil))('R) * (3)
                & (
                if (ctr1.interface.piOut.size == 0) cohide(1) & boxTrue(1)
                else (boxAnd('R) & andR('R)
                  < (skip, ComposeProofStuff.closeSide(side1)('R) & prop)) * (ctr1.interface.piOut.size - 1)
                  & ComposeProofStuff.closeSide(side1)('R) & prop
                )
              //closed!
            ) & (if (PRINT_STEP) print("C2;C1 done!") else skip)
          )

        ),
        //pre boot - DONE
        //TODO does this master() always close, or should I try to reduce the thing further? (how??)
        hideL(-1) & composeb('R) & G('R) & master() //& print("boot closed?")
      ),
      //global - DONE
      V('R) & prop & (if (PRINT_STEP) print("global closed?") else skip)
    )
      & (if (PRINT_STEP) print("step done?") else skip)
    )

    //Return verified composite contract
    return ctr3
  }

  object ComposeProofStuff {


    def recomposeDP(vDelta: Seq[Seq[Variable]]): DependentPositionTactic = "Recompose Delta Part" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(_, _)) =>
        var t: BelleExpr = (if (PRINT_RECOMPOSE_DP) print("recomposeDP: recomposing dp") else skip)
        var h = oneList(0)
        var cnt = 0
        vDelta.foreach((vs: Seq[Variable]) => {
          t = t & (if (PRINT_RECOMPOSE_DP) print("recomposeDP: recomposing single dp -> " + vs) else skip) &
            useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos, h) * (vs.size - 1) &
            (if (PRINT_RECOMPOSE_DP) print("recomposeDP: done") else skip)
          h = 1 :: h
        })
        t = t & (if (PRINT_RECOMPOSE_DP) print("recomposeDP: recomposing dmps") else skip) &
          useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos) * Math.max(vDelta.size - 1, 0)
        t & (if (PRINT_RECOMPOSE_DP) print("recomposeDP: done recomposing dp") else skip)
    })

    def dropDeltaParts(remEmpty: Boolean, keepEmpty: Boolean, remInit: Seq[Variable], dCnt: Int, sCnt: Int): DependentPositionTactic = "Drop Delta Part" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(_, _)) =>
        var t: BelleExpr = skip
        //if remEmpty --> empty remDP, nothing to remove
        if (!remEmpty) {
          //there is something in remDP, so remove it
          if (keepEmpty) {
            //empty keepDP, so drop all and introduce ?true;
            //TODO UNTESTED!
            t = t & Lemmas.lemma1(1) & (if (PRINT_DROP_DELTA_PARTS) print("dropDeltaParts: ???") else skip) &
              Lemmas.lemma5LT("true".asFormula)(1) & (if (PRINT_DROP_DELTA_PARTS) print("dropDeltaParts: ???") else skip) //< (skip & print("hihi1"), boxTrue(1)& print("hihi2"))
          }
          else {
            //there is something in remDP and keepDP, so we have to check what to remove
            t = t & (if (PRINT_DROP_DELTA_PARTS) print("dropDeltaParts: dropping dp: " + remInit) else skip) & ComposeProofStuff.dropDeltaPartForPort(remInit, dCnt, sCnt)(1)
          }
        }
        t
    })

    def dropDeltaPartForPort(vInit: Seq[Variable], dCnt: Int, sCnt: Int): DependentPositionTactic = "Drop Delta Part For Port" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(dp: Compose, b: Box)) =>
        //        val cnt: Int = countBinary[Compose](dp)
        var t: BelleExpr = (if (PRINT_DROP_DELTA_PART_FOR_PORT) print("dropDeltaPartForPort: composing " + dCnt) else skip) &
          (composeb(pos.top.getPos) &
            (composeb(pos.top.getPos, 1 :: Nil) *)) * Math.max(dCnt - 1, 0) & (composeb(pos.top.getPos) *)
        t = t & (if (PRINT_DROP_DELTA_PART_FOR_PORT) print("dropDeltaPartForPort: dropOrSkip " + sCnt) else skip)
        ((sCnt - 1).until(0, -1)) foreach (i => {
          t = t & dropOrSkipDeltaPart(vInit)(pos.top.getPos, oneList(i))
        })
        t = t & (if (PRINT_DROP_DELTA_PART_FOR_PORT) print("dropDeltaPartForPort: last one...") else skip)
        t = t & dropOrSkipDeltaPart(vInit)(pos.top.getPos)
        t
    })


    def dropOrSkipDeltaPart(vInit: Seq[Variable]): DependentPositionTactic = "Drop From Delta Part" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(a: Assign, _)) =>
        if (vInit.contains(a.x)) {
          (if (PRINT_DROP_OR_SKIP_DELTA_PART) print("dropOrSkipDeltaPart: removing dp '" + a.x + "'") else skip) & Lemmas.lemma1(pos) & (if (PRINT_DROP_OR_SKIP_DELTA_PART) print("dropOrSkipDeltaPart: done removing") else skip)
        }
        else {
          (if (PRINT_DROP_OR_SKIP_DELTA_PART) print("dropOrSkipDeltaPart: skipping dp '" + a.x + "'") else skip)
          //          useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos)
        }
    })

    def dropRemainingPorts3(vIn: Seq[Seq[Variable]], X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]]): DependentPositionTactic = "Drop Remaining Ports3" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, b: Box)) =>
        var t: BelleExpr = (if (PRINT_DROP_REMAINING_PORTS3) print("dropRemainingPorts3: dropping p3...") else skip)
        vIn.foreach(vi => {
          if (X.contains(vi)) {
            t = t & dropFromPorts3(vi, X(vi))(pos)
          }
        })
        t
    })

    def dropFromPorts3(vi: Seq[Variable], vo: Seq[Variable]): DependentPositionTactic = "Drop From Ports3" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, b: Box)) =>
        var t: BelleExpr = (if (PRINT_DROP_FROM_PORTS3) print("dropFromPorts3: dropping reamining ports3, port=" + vi) else skip)
        //TODO check
        //remove all ports from front to back
        // because this way, the removal of a port does not change the position of the other ports
        //        vi.reverse.foreach(v => {
        val mpa = MultiPort.assign(vi, vo)
        val assPos = posOf(b, ((x: Program) => x.equals(mpa)))
        //                    val assPos = posOfAssign(b, v)
        if (assPos > 0) {
          //the assignment was found
          t = t & (if (PRINT_DROP_FROM_PORTS3) print("dropFromPorts3: dropping at " + assPos) else skip) & Lemmas.lemma1(1, oneList(assPos)) & (if (PRINT_DROP_FROM_PORTS3) print("dropFromPorts3: dropped") else skip)
        }
        //        })
        t
    })

    def dropIn(vInDrop: mutable.Seq[Seq[Variable]], vInAll: mutable.Seq[Seq[Variable]]): DependentPositionTactic = "Drop Input Ports" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(_, Box(in3: Compose, _))) =>
        //TODO check
        //        val n = countBinary[Compose](in3.asInstanceOf[Compose])
        val n = vInAll.size
        var t: BelleExpr = skip
        if (n > 1) {
          //          t = t & composeb(pos.top.getPos, 1 :: Nil) * (n / 2)
          //          t = t & (dropOrMerge(vInDrop)(pos.top.getPos) * ((n / 2) + 1))
          t = t & composeb(pos.top.getPos, 1 :: Nil) * (n - 1)
          t = t & dropOrMerge(vInDrop)(pos.top.getPos) * n
        }
        else {
          t = t & (dropOrMerge(vInDrop)(pos.top.getPos) * n)
        }
        if (n == vInDrop.size && vInDrop.nonEmpty) {
          t = t & (if (PRINT_DROP_IN) print("dropIn: introduceEmptyTest in dropIn, n=" + n + ", vIn.size=" + vInDrop.size + ", vIn=" + vInDrop) else skip) &
            Lemmas.lemma5T("true".asFormula)(pos.top) & (if (PRINT_DROP_IN) print("dropIn: after lemma5") else skip) <
            (skip, (if (PRINT_DROP_IN) printIndexed("dropIn: before boxTrue") else skip) & cohide(1) & boxTrue(1) & (if (PRINT_DROP_IN) print("dropIn: after boxTrue") else skip))
        }
        t & (if (PRINT_DROP_IN) print("dropIn: done") else skip)
      //no inputs --> let the test stay there
      case Some(Box(_, Box(in3: Test, _))) => useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top) //Lemmas.lemma1AB(pos.top.getPos)
    })

    def dropOrMerge(vIn: mutable.Seq[Seq[Variable]]): DependentPositionTactic = "Drop Or Merge" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(_, Box(b, _))) =>
        var t: BelleExpr = (if (PRINT_DROP_OR_MERGE) print("dropOrMerge: ...") else skip)
        if (v(b).intersect(vIn.flatten).nonEmpty) {
          t = t & Lemmas.lemma1AB(pos.top.getPos)
        }
        else {
          t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos)
        }
        t
    })

    def closeSide(side: mutable.Map[Seq[Variable], Provable]): DependentPositionTactic = "Close With Sidecondition" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(Compose(Compose(Compose(dp, ctrl), told), plant), True)) =>
        (if (PRINT_CLOSE_SIDE) print("CLOSE SIDE 0 - true") else skip) & boxTrue
      case Some(Box(Compose(Compose(Compose(dp, ctrl), told), plant), out)) => {
        val s = side.keySet.filter((vs: Seq[Variable]) => {
          vs.intersect(v(out)).nonEmpty
        })
        require(s.size == 1, "Wrong number of side conditions (" + s.size + ") for out=" + out)
        val p = side(s.last)
        (if (PRINT_CLOSE_SIDE) print("CLOSE SIDE 1") else skip) & composeb('R) * 3 &
          (if (PRINT_CLOSE_SIDE) print("CLOSE SIDE 2 - " + p) else skip) & useAt("ANON", p, PosInExpr(1 :: Nil))('R) &
          (if (PRINT_CLOSE_SIDE) print("CLOSE SIDE 3") else skip) & closeId &
          (if (PRINT_CLOSE_SIDE) print("CLOSE SIDE 4") else skip)
      }
    })

    def introduceAndWeakenForAll(piIn: LinkedHashMap[Seq[Variable], Formula], piOut: LinkedHashMap[Seq[Variable], Formula], X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]], cpoT: mutable.Map[(Seq[Variable], Seq[Variable]), Provable], vIn3: Seq[Seq[Variable]]): DependentPositionTactic = "Introduce And Weaken For All" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, Box(in, Box(ports, Box(ports3, _))))) =>
        var t: BelleExpr = (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll") else skip)
        val vInCon: mutable.LinkedHashMap[Seq[Variable], Formula] = piIn.filter((e) => X.keySet.contains(e._1))
        val vOutCon: mutable.LinkedHashMap[Seq[Variable], Formula] = piOut.filter((e) => X.values.toSet.contains(e._1))
        val vInOpen: mutable.LinkedHashMap[Seq[Variable], Formula] = piIn.filter((e) => !X.keySet.contains(e._1))

        if (X.isEmpty) {
          //no connected ports, so nothing to move -> just remove empty test
          // nevertheless continue, to split all the parts as needed!
          t = t & Lemmas.lemma1(1, 1 :: 1 :: Nil)
        }

        //[p][in1][ports1][mports3]A
        var nPorts3 = X.size
        val hPorts3 = oneList(3)
        if (nPorts3 > 1) {
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: goPorts3 - " + Math.max(0, nPorts3 - 1) + " times") else skip) & composeb(pos.top.getPos, hPorts3) * Math.max(0, nPorts3 - 1) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: wentPorts3") else skip)
        }

        //[p][in][ports][ports3-1]...[ports3-nPorts3]A
        val nPorts = if (ports.isInstanceOf[Compose]) {
          //multiple assignments --> compose
          (countBinary[Compose](ports.asInstanceOf[Compose]) + 1)
        }
        else if (ports.isInstanceOf[Assign]) {
          //single assignment
          1
        }
        else {
          //no assignment, but empty test
          0
        }
        var hPorts1 = 1 :: 1 :: Nil
        if (nPorts > 1) {
          //TODO maybe use * instead of foreach?
          //          (0 until nPorts1 - 1) foreach (i => {
          //            t = t & print("goPorts " + i) & composeb(pos.top.getPos, hPorts1) & print("wentPorts " + i)
          //            //            hPorts = 1 :: hPorts
          //          })
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: goPorts - " + Math.max(0, nPorts - 1) + " times") else skip) & composeb(pos.top.getPos, hPorts1) * Math.max(0, nPorts - 1) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: wentPorts") else skip)
        }

        //[p][in][ports-1]...[ports-nPorts][ports3-1]...[ports3-nPorts3]A
        var hIn = 1 :: Nil
        var nIn = 0

        //TODO Check
        //        if (in.isInstanceOf[Compose]) {
        if (vInOpen.size > 0) {
          //in is not empty
          //TODO Check
          //          nIn = (countBinary[Compose](in.asInstanceOf[Compose]) + 1) / 2
          nIn = vInOpen.size
          // compose in1 into pieces. for each port there is are several randombs and a test. so we have n-1 groups of statements.
          // each group is separated and then split.
          (0 until nIn - 1) foreach (i => {
            //TODO Check
            //            t = t & (print("goIn" + i) & composeb(pos.top.getPos, hIn)) * 2
            t = t & (((if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: goIn" + i) else skip) & composeb(pos.top.getPos, hIn)) *)
            hIn = 1 :: 1 :: hIn
          })
          //TODO Check
          //          t = t & print("go last") & composeb(pos.top.getPos, hIn) & print("go done") & print("done with introduceAndWeakenForAll")
          t = t & (((if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: goIn last") else skip) & composeb(pos.top.getPos, hIn)) *) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: goIn done") else skip)
        }

        //ports connected --> something to do!
        if (vInCon.nonEmpty) {
          //[p][random-in-1]...[random-in-1][test-in-1]...[random-in-nIn]...[random-in-nIn][test-in-nIn][ports-1]...[ports-nPorts][mports3-1]...[mports3-nPorts3]A
          var donePorts = Seq.empty[Seq[Variable]]
          vInCon.foreach((e) => {
            //            val inPos = if (piIn.keys.toSeq.indexOf(e._1) == 0) 0 else piIn.keys.toSeq.take(piIn.keys.toSeq.indexOf(e._1) - 1).flatten.size
            val currIn = piIn.keys.toSeq.intersect(vIn3 ++ donePorts ++ Seq(e._1))
            val inPos = if (currIn.indexOf(e._1) == 0) 0 else currIn.take(currIn.indexOf(e._1)).flatten.size + currIn.take(currIn.indexOf(e._1)).size
            if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) {
              println("--- introduceAndWeakenForAll ---")
              println("currIn: " + currIn)
              println("looking for position of " + e._1)
              println("currIn.indexOf(e._1)=" + currIn.indexOf(e._1))
              println("currIn.take(currIn.indexOf(e._1) - 1)=" + currIn.take(currIn.indexOf(e._1)))
              println("and inPos=" + inPos)
            }
            val portPos = X.keys.toSeq.diff(donePorts).indexOf(e._1)
            val cntIn = vInOpen.keySet.flatten.size + vInOpen.size + donePorts.flatten.size + donePorts.size
            val cntPorts = if (nPorts == 0) 1 else nPorts
            val cntPorts3 = if (nPorts3 == 0) 1 else nPorts3
            t = t & ComposeProofStuff.introduceTestFor(e._1, e._2, X.get(e._1).get, vOutCon.get(X.get(e._1).get).get,
              nIn, cntIn, nPorts, cntPorts, nPorts3, cntPorts3,
              inPos, portPos, cpoT((e._1, X(e._1))),
              Seq(X.keys.filter(v => !donePorts.contains(v)).toSeq: _*))(pos.top.getPos)
            donePorts = donePorts ++ Seq(e._1)
            nIn = nIn + 1
            nPorts3 = nPorts3 - 1
          })
        }
        t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR_ALL) print("introduceAndWeakenForAll: done with introduceAndWeakenForAll") else skip)

      case _ => print("introduceAndWeakenForAll: ERROR ALL")
    })


    def introduceTestFor(vIn: Seq[Variable], tIn: Formula, vOut: Seq[Variable], tOut: Formula,
                         nIn: Int, cntIn: Int, nPorts: Int, cntPorts: Int, nPorts3: Int, cntPorts3: Int,
                         inPos: Int, portPos: Int, cpo: Provable,
                         Xin: Seq[Seq[Variable]]): DependentPositionTactic
    = "Introduce And Weaken For" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(p, _)) =>
        //Initially we have:
        //[p][random-in-1]...[random-in-1][test-in-1]......[random-in-nIn]...[random-in-nIn][test-in-nIn][ports-1]...[ports-nPorts][ports3-1]...[ports3-nPorts3]A
        //        val cntIn = if (nIn == 0) 0 else nIn * 2
        //        val cntPorts = if (nPorts == 0) 1 else nPorts
        //        val cntPorts3 = if (nPorts3 == 0) 1 else nPorts3

        //introduce test using lemma 5
        var t: BelleExpr = (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: start introduceTestFor: vIn=" + vIn + "(vOut=" + vOut + ") --> " + tIn + "(tOut=" + tOut + ") @pos=" + pos + ", with: nIn=" + nIn + ", cntIn=" + cntIn + ", nPorts=" + nPorts + ", cntPorts=" + cntPorts + ", nPorts3=" + nPorts3 + ", inPos=" + inPos + ", portPos=" + portPos) else skip)
        //if nIn is zero, we have just a ?true test as in3 -> remove this test, it will be replaced with actual ports
        if (nIn == 0) {
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: remove empty in3") else skip) & Lemmas.lemma1(1, 1 :: Nil)
        }
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: introduce test") else skip) & Lemmas.lemma5T(tOut)(pos) < (skip, hide(-2) * 4 & implyRi & CMon(PosInExpr(1 :: Nil)) & prop) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done introducing") else skip)
        //split test from p
        t = t & composeb(pos)
        //now: [p][test][in...][ports...][ports3...]A

        //commute test through in3
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute through in3, nIn=" + nIn + ", cntIn=" + cntIn) else skip)
        var h = 1 :: Nil
        if (nIn != 0) {
          //there are some ports in in3, so we commute randomb;...;randomb;testb;...
          (0 until cntIn) foreach (_ => {
            t = t & (Lemmas.lemma4_4T(pos.top.getPos, h) | Lemmas.lemma4_6T(pos.top.getPos, h)) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commuted in3") else skip)
            h = 1 :: h
          })
        }
        else {
          //there is no port in in3, so nothing to do, since we removed ?true
        }
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done with in3") else skip)

        //commute test with ports
        //TODO test case with actual portsX!
        require(nPorts == 0, "so far only atomic components can be composed")
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute through portsX, nPortsX=" + nPorts + ", cntPortsX=" + cntPorts + " --> assumed to be empty!") else skip)
        h = oneList(1 + cntIn)
        t = t & Lemmas.lemma4_6T(pos.top.getPos, h)

        //        if (nPorts != 0) {
        //          //there are some ports in portsX, so we commute randomb;testb;...
        //          (0 until nPorts3) foreach (i => {
        //            t = t & print("a") & Lemmas.lemma4_4T(pos.top.getPos, h)
        //            h = 1 :: h
        //          })
        //        }
        //        else {
        //          //TODO beware! if there have been multiple compositions, we might have multiple ?true tests mixed with actual connections --> DROP ?true test from contract on composition?
        //          //there is no port in portsX, so we just commute the ?true;
        //          t = t & print("d") & Lemmas.lemma4_6T(pos.top.getPos, h)
        //        }
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done with portsX") else skip)

        //locate v in ports and move test there
        //        val assPos = posOfAssign(seq.sub(pos).get.asInstanceOf[Box], vIn.last) - (if (nIn == 0) 1 else 0)
        //position of assignment group of multiport--> if in3 was just an empty test, this test has been removed --> reduce by 1
        val assPos = 1 + cntIn + cntPorts + portPos
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute to position in ports3, cntIn=" + cntIn + ", cntPorts=" + cntPorts + ", portPos=" + portPos + ", assPos=" + assPos) else skip)
        //TODO check
        //      h = oneList(1 + cntIn + cntPorts)
        (1 + cntIn + cntPorts to assPos) foreach (i => {
          // multiport I am commuting with
          val vCurr = Xin(i - (1 + cntIn + cntPorts))
          // split multiport assignments
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: splitting, i=" + i + ", vCurr=" + vCurr) else skip)
          t = t & composeb(pos.top.getPos, oneList(i + 1)) * (vCurr.size - 1)
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: split") else skip)
          // commute test with all assignments
          (i until (i + vCurr.size)) foreach (j => {
            t = t & Lemmas.lemma4_5T(pos.top.getPos, oneList(j))
            t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commuted ports3...") else skip)
          })
          // reconnect multiport assignments
          t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos, oneList(i)) * (vCurr.size - 1)
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: reconnected") else skip)

          // go to next multiport
          //          h = 1 :: h
        })
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done moving to position in ports3") else skip)

        //weaken test
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: weakening test") else skip)
        t = t & Lemmas.lemma6T(tIn)(pos.top.getPos, oneList(assPos + 1)) < (
          skip
          ,
          (useAt("[;] compose", PosInExpr(1 :: Nil))('R) *) & composeb('R)
            & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: using cpo=" + cpo) else skip)
            & useAt("ANON", cpo, PosInExpr(1 :: Nil))(1, 1 :: Nil)
            & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: used cpo") else skip)
            //[dp3;(ctrl1;ctrl2);told;plant3;in;ports;ports3*]A
            //remove all remaining parts of ports3*, and all of ports and in, and plant3, told and (ctrl1;ctr2).
            & ((composeb('R) & Lemmas.lemma1AB(1)) * (assPos + 2))
            & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: removed remaining parts") else skip)
            //next, apply all assignments in dp3
            & (((composeb('R) | assignb('R) | (testb('R) & useAt(DerivedAxioms.trueImplies, PosInExpr(0 :: Nil))('R))) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("step...") else skip)) *)
            //            & ((composeb('R) *) & (( ( (composeb(1,1::Nil)*) & (assignb('R)*) ) | (testb('R) & useAt(DerivedAxioms.trueImplies, PosInExpr(0 :: Nil))('R))) *))
            //            & ((( (composeb('R)&print("composed"))  | (skip&print("skipped")) ) & ( (assignb('R)&print("assigned")) | (testb('R)&print("tested") & useAt(DerivedAxioms.trueImplies, PosInExpr(0 :: Nil))('R)))) *)
            //now QE should close the thing
            //TODO DOES IT?
            & hide(-1)
            & QE
        ) & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done weakening") else skip)

        //[p][in...][ports...][ports3*...]A
        //make assignment non-deterministic
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: make non-det") else skip)
        // split multiport assignments
        t = t & composeb(pos.top.getPos, oneList(assPos)) * (vIn.size - 1)
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: split") else skip)
        // commute test with all assignments
        (assPos until (assPos + vIn.size)) foreach (j => {
          //          t = t & useAt(Lemmas.lemma3, PosInExpr(1 :: Nil))(1, oneList(j))
          t = t & useAt("ANON", Lemmas.lemma3.fact, PosInExpr(1 :: Nil))(1, oneList(j))
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: made non-det...") else skip)
        })
        //        t = t & useAt(Lemmas.lemma3, PosInExpr(1 :: Nil))(1, oneList(assPos))
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done making non-det") else skip)

        //[p][in...][ports...][ports3*...]A
        //rotate new non-det assignments to designated position
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute new non-det ports to designated position") else skip)
        (0 until vIn.size) foreach (k => {
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute - " + k) else skip)
          //  1) commute non-det assign with remaining ports3
          (k + cntIn + cntPorts + portPos).until(k + cntIn + cntPorts, -1) foreach (i => {

            // multiport I am commuting with
            val vCurr = MultiPort.multiportAtPosition(Xin, i - (k + cntIn + cntPorts + 1))
            // split multiport assignments
            t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: splitting - vCurr=" + vCurr + ", i=" + i) else skip)
            t = t & composeb(pos.top.getPos, oneList(i)) * (vCurr.size - 1)
            t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: split") else skip)
            // commute test with all assignments
            (i + vCurr.size - 1).until(i - 1, -1) foreach (j => {
              t = t & Lemmas.lemma4_3T(pos.top.getPos, oneList(j))
              t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commuted...") else skip)
            })
            // reconnect multiport assignments
            t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos, oneList(i + 1)) * (vCurr.size - 1)
            t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: reconnected") else skip)

            //            t = t & Lemmas.lemma4_3T(1, oneList(i))
          })
          //  2) commute non-det assign with portsX
          //  TODO test case with actual portsX!
          if (nPorts == 0) {
            //its just a test
            t = t & Lemmas.lemma4_4T(1, oneList(k + cntIn + cntPorts))
          }
          else {
            //there are actual ports in portsX
            (k + cntIn + cntPorts).until(k + inPos, -1) foreach (i => {
              t = t & Lemmas.lemma4_3T(1, oneList(i))
            })
          }
          //  3) commute non-det assign with in
          if (nIn != 0) {
            //there are actual open ports
            //TODO check
            //          (cntIn).until(inPos * 2, -2) foreach (i => {
            //            t = t & Lemmas.lemma4_4T(1, oneList(i)) & Lemmas.lemma4_2T(1, oneList(i - 1))
            //          })
            (k + cntIn).until(k + inPos, -1) foreach (i => {
              t = t & (Lemmas.lemma4_4T(1, oneList(i)) | Lemmas.lemma4_2T(1, oneList(i)))
            })
          }
        })
        //        // reconnect multiport assignments
        //        t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos,oneList(inPos+1))*(vIn.size-1)
        //        t = t & print("reconnected")


        //rotate test to designated position
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute test to designated position") else skip)
        //  1) commute test with remaining ports3
        (cntIn + cntPorts + portPos + vIn.size).until(cntIn + cntPorts + vIn.size, -1) foreach (i => {

          // multiport I am commuting with
          val vCurr = MultiPort.multiportAtPosition(Xin, i - (cntIn + cntPorts + vIn.size) - 1)
          // split multipornt assignments
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: splitting - vCurr=" + vCurr + ", i=" + i) else skip)
          t = t & composeb(pos.top.getPos, oneList(i)) * (vCurr.size - 1)
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: split") else skip)
          // commute test with all assignments
          (i + vCurr.size - 1).until(i - 1, -1) foreach (j => {
            t = t & Lemmas.lemma4_5T(pos.top.getPos, oneList(j))
            t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commuted...") else skip)
          })
          // reconnect multiport assignments
          t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos, oneList(i + 1)) * (vCurr.size - 1)
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: reconnected") else skip)

          //          t = t & Lemmas.lemma4_5T(1, oneList(i))
        })
        //  2) commute test with ports
        if (nPorts == 0) {
          //its just a test
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commuting test with ports") else skip)
          t = t & Lemmas.lemma4_6T(1, oneList(cntIn + cntPorts + vIn.size))
        }
        else {
          //TODO NOT implemented
          throw new NotImplementedError("Composition for non-atomic components is not yet implemented!")
          //          //there are actual ports in portsX
          //          (cntIn + cntPorts + 1).until(inPos + 1, -1) foreach (i => {
          //            t = t & Lemmas.lemma4_5T(1, oneList(i))
          //          })
        }
        //  3) commute test with in
        if (nIn != 0) {
          t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commuting test with in") else skip)
          //there are actual open ports
          //TODO check
          //          (cntIn + 1).until(inPos * 2 + 1, -2) foreach (i => {
          //            t = t & Lemmas.lemma4_6T(1, oneList(i)) & Lemmas.lemma4_4T(1, oneList(i - 1))
          //          })
          (cntIn + vIn.size).until(inPos + vIn.size, -1) foreach (i => {
            t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: commute " + i) else skip)
            t = t & (Lemmas.lemma4_6T(1, oneList(i)) | Lemmas.lemma4_4T(1, oneList(i)))
          })
        }
        t = t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done commute test to designated position") else skip)

        t & (if (PRINT_INTRODUCE_AND_WEAKEN_FOR) print("introduceTestFor: done with introduceTestFor") else skip)

      case _ => print("ERROR")
    })

    def posOf[C <: Program](b: Box, t: C => Boolean): Int = {
      b match {
        case Box(b, f) if b.isInstanceOf[C] & t(b.asInstanceOf[C]) => 1
        case Box(x, b2: Box) => posOf(b2, t) + 1
        case _ => Int.MinValue
      }
    }

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

    //    def dropDeltaParts(cnt: Int, left: Boolean): DependentPositionTactic = "Remove DeltaParts" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    //      case Some(Box(dp, f: Formula)) =>
    //        var t: BelleExpr = skip //print("removeDP!")
    //        //        println("compose # " + countCompose(dp.asInstanceOf[Compose]))
    //        if (dp.isInstanceOf[Test]) {
    //          //          println("[removeDeltaParts]: Just a test, so nothing to do here.")
    //        }
    //        else if (dp.isInstanceOf[Assign]) {
    //          //          println("[removeDeltaParts]: Just a single assignment...")
    //          if (cnt == 1) {
    //            t = t & Lemmas.lemma1BA(pos)
    //            t = t & introduceEmptyTest(pos, seq, f)
    //          }
    //        }
    //        else {
    //          val nr = countBinary[Compose](dp.asInstanceOf[Compose])
    //          //          println("[removeDeltaParts]: Multiple (nr=" + (nr + 1) + ") assignments...")
    //          if (cnt == 0) {
    //            //            println("[removeDeltaParts]: Nothing to do, since cnt=" + cnt + "...")
    //          }
    //          else {
    //            if (cnt == nr + 1) {
    //              t = t & Lemmas.lemma1BA(pos.top.getPos)
    //              t = t & introduceEmptyTest(pos, seq, f)
    //            }
    //            else {
    //              val newCnt = if (!left)
    //                nr + 1 - cnt
    //              else
    //                cnt
    //              var s: List[Int] = Nil
    //              (0 until newCnt) foreach (i => {
    //                t = t & composeb(pos.top.getPos, s)
    //                if (left) t = t & Lemmas.lemma1BA(pos.top)
    //                else s = List(1) ++ s
    //              })
    //              if (!left) {
    //                (0 until newCnt - 1) foreach (i => {
    //                  t = t & useAt("[;] compose", PosInExpr(1 :: Nil))(pos.top.getPos)
    //                })
    //                if (newCnt != 0) t = t & Lemmas.lemma1AB(pos.top.getPos)
    //                else t = t & Lemmas.lemma1BA(pos.top.getPos)
    //              }
    //            }
    //          }
    //        }
    //        //        t = t & print("done!")
    //        t
    //    })

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
    //    TactixLibrary.proveBy("[a:=a1;b:=b1;]b>0".asFormula, print("a") & ComposeProofStuff.dropDeltaParts(0, false)('R))
    ProofHelper.shutdownProver
  }

  /**
    * Create the ports part for the composit contract.
    *
    * @param X The port mapping.
    * @tparam C The type of contract to be composed, as only contracts of the same type can be composed.
    * @return The ports part of the composit.
    */
  def composedPorts[C <: Contract](X: mutable.LinkedHashMap[Seq[Variable], Seq[Variable]]): Program = {
    X.map(x => MultiPort.assign(x._1, x._2)) match {
      case p if p.nonEmpty => p.reduce((a1, a2) => Compose(a1, a2))
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
  private def composedInvariant[C <: Contract](ctr1: C, ctr2: C, X: mutable.Map[Seq[Variable], Seq[Variable]]): And = {
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
  private def composedPre[C <: Contract](ctr1: C, ctr2: C, X: mutable.Map[Seq[Variable], Seq[Variable]]): And = {
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
  private def composedBootstrap[C <: Contract](X: mutable.Map[Seq[Variable], Seq[Variable]]): Formula = {
    if (X.isEmpty) {
      return "true".asFormula
    }
    else {
      return X.map { case (in, out) => MultiPort.equals(in, out) }.reduce((a: Formula, b: Formula) => And(a, b))
    }
  }
}
