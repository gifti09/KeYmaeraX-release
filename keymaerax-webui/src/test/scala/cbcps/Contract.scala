package cbcps

import java.io._
import java.text.Normalizer.Form

import Utility._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.LemmaID
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.btactics.TreeForm.Var
import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXPrettyPrinter}
import ProofHelper._

import scala.collection.immutable.ListMap
import scala.util.Try

/**
  * Created by andim on 25.07.2016.
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

  def proofGoals(): IndexedSeq[Sequent]

  def baseCaseProofGoal() = proofGoals()(0)

  def useCaseProofGoal() = proofGoals()(1)

  def stepProofGoal() = proofGoals()(2)

  def isBaseCaseVerified(): Boolean = baseCaseLemma match {
    case Some(l) => true
    case _ => false
  }

  def isUseCaseVerified(): Boolean = useCaseLemma match {
    case Some(l) => true
    case _ => false
  }

  def isStepVerified(): Boolean = stepLemma match {
    case Some(l) => true
    case _ => false
  }

  def verifyBaseCase(l: Lemma): Boolean = verifyBaseCase(l, true)

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

  def verifyUseCase(l: Lemma): Boolean = verifyUseCase(l, true)

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

  def verifyStep(l: Lemma): Boolean = verifyStep(l, true)

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

  def verifyBaseCase(id: LemmaID): Boolean = {
    loadLemma(id) match {
      case Some(l: Lemma) => verifyBaseCase(l)
      case _ => false
    }
  }

  def verifyUseCase(id: LemmaID): Boolean = {
    loadLemma(id) match {
      case Some(l: Lemma) => verifyUseCase(l)
      case _ => false
    }
  }

  def verifyStep(id: LemmaID): Boolean = {
    loadLemma(id) match {
      case Some(l: Lemma) => verifyStep(l)
      case _ => false
    }
  }

  val BC_NAME: String = "-BaseCase"
  val UC_NAME: String = "-UseCase"
  val S_NAME: String = "-Step"


  def verifyBaseCase(t: BelleExpr): Option[Lemma] = {
    val x = verify(baseCaseProofGoal(), t, Some(component.name + BC_NAME))
    x match {
      case Some(l) => verifyBaseCase(l)
      case _ =>
    }
    x
  }

  def verifyUseCase(t: BelleExpr): Option[Lemma] = {
    val x = verify(useCaseProofGoal(), t, Some(component.name + UC_NAME))
    x match {
      case Some(l) => verifyUseCase(l)
      case _ =>
    }
    x
  }

  def verifyStep(t: BelleExpr): Option[Lemma] = {
    val x = verify(stepProofGoal(), t, Some(component.name + S_NAME))
    x match {
      case Some(l) => verifyStep(l)
      case _ =>
    }
    x
  }

  def contract(): Formula

  def isVerified() = isBaseCaseVerified() && isUseCaseVerified() && isStepVerified()

  def sideCondition(ctr2: Contract, X: Map[Variable, Variable]): Formula

  def cpo(ctr2: Contract, X: Map[Variable, Variable]): Map[(Variable, Variable), Formula]

  def contractPre(): Formula

  def contractPlant(): ODESystem

  def contractPlant(thePlant: ODESystem): ODESystem

  def contractPost(): Formula
}

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

class DelayContract(component: Component, interface: Interface, pre: Formula, post: Formula, invariant: Formula, baseCaseLemma: Option[Lemma] = None, useCaseLemma: Option[Lemma] = None, stepLemma: Option[Lemma] = None)
  extends Contract(component, interface, pre, post, invariant, baseCaseLemma, useCaseLemma, stepLemma) {

  override def contractPlant(): ODESystem = {
    contractPlant(component.plant)
  }

  override def contractPlant(thePlant: ODESystem): ODESystem =
    ODESystem(DifferentialProduct(Globals.plantT, thePlant.ode), And(thePlant.constraint, Globals.consT))


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
    * Extracts the proof goals that need to be closed in order to verify the delay contract.
    */
  lazy val _proofGoals: IndexedSeq[Sequent] = {
    val t: BelleExpr = implyR('R) & loop(invariant)('R) < ( //& andL('L) *@ TheType()
      andLi *@ TheType() & cut(contractPre()) <
        (hideL(-1) & implyRi partial, hideR(1) & QE) partial, //& print("Base case")
      andLi *@ TheType() & cut(invariant) <
        (hideL(-1) & implyRi partial, hideR(1) & QE) partial, //& print("Use Case")
      andLi *@ TheType() & cut(invariant) <
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

  // \varphi -> [delta-part][ctrl][t0:=t][{t'=1,plant & t-t0<=\varepsilon}] \Pi_out
  override def sideCondition(ctr2: Contract, X: Map[Variable, Variable]): Formula = Imply(
    this.invariant,
    Box(
      Interface.compose(this.interface, ctr2.interface, X).deltaPart,
      Box(Component.compose(this.component, ctr2.component, Contract.composePorts(X)).ctrl,
        Box(Globals.oldT,
          Box(this.contractPlant(Component.compose(this.component, ctr2.component, Contract.composePorts(X)).plant), this.interface.piOutAll)
        )
      )
    )
  )


  override def cpo(ctr2: Contract, X: Map[Variable, Variable]): Map[(Variable, Variable), Formula] = {
    //useless and just to avoid errors
    val ctr1 = this
    var s = Map.empty[(Variable, Variable), Formula]

    require(X.keySet.subsetOf(ctr1.interface.vIn ++ ctr2.interface.vIn) || !X.values.toSet.subsetOf(ctr1.interface.vOut ++ ctr2.interface.vOut),
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

object Contract {

  def save(ctr: Contract, fName: String) = {
    val stream = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    stream.writeObject(new SerializableContract(ctr))
    stream.close()
  }

  def load(fName: String): Contract = {
    val stream = new ObjectInputStream(new FileInputStream(new File(fName)))
    val ret = stream.readObject().asInstanceOf[SerializableContract].contract()
    stream.close()
    return ret
  }

  def admissible(component: Component, interface: Interface): Boolean = {
    bv(component.ctrl).intersect(interface.vDelta).isEmpty &&
      (bv(component.ctrl) ++ bv(component.plant) ++ bv(component.ports)).intersect(interface.vInit).isEmpty &&
      (bv(component.ctrl) ++ bv(component.plant)).intersect(interface.vIn).isEmpty
  }

  //TODO check before use
  def changeContract(component: Component, interface: Interface, pre: Formula, post: Formula): Formula = {
    Imply(
      Globals.appendGlobalPropertyToFormula(pre),
      Box(Loop(
        Compose(Compose(Compose(Compose(interface.deltaPart, component.ctrl), component.plant), interface.in), component.ports)), post)
    )
  }

  private val preTactic = andLi *@ TheType() & implyRi

  /**
    * Extracts the proof goals that need to be closed in order to verify the change contract.
    *
    * @param component The component.
    * @param interface The admissible interface.
    * @param pre       The initial condition.
    * @param post      The safety property.
    * @param inv       The loop invariant used.
    * @return Three proof goals: base case, use case, step.
    */
  def changeProofGoals(component: Component, interface: Interface, pre: Formula, post: Formula, inv: Formula): IndexedSeq[Sequent] = {
    val t: BelleExpr = implyR('R) & loop(inv)('R) < ( //& andL('L) *@ TheType()
      preTactic partial, //& print("Base case")
      preTactic partial, //& print("Use Case")
      preTactic partial //& print("Step")
      )
    val p = proveBy(changeContract(component, interface, pre, post), t)
    p.subgoals
  }

  def compose[C <: Contract](ctr1: C, ctr2: C, X: Map[Variable, Variable], cpoT: Map[(Variable, Variable), BelleExpr], side1T: BelleExpr, side2T: BelleExpr): C = {
    //Initial checks
    require(ctr1.getClass.equals(ctr2.getClass), "only contracts of the same type can be composed")
    require(ctr1.isVerified() && ctr2.isVerified(), "only verified contracts can be composed")

    //Compose all parts of the contract
    val ports: Program = composePorts(X)
    val i3 = Interface.compose(ctr1.interface, ctr2.interface, X)
    val c3 = Component.compose(ctr1.component, ctr2.component, ports)
    val pre3 = composePre(ctr1, ctr2, X)
    val post3 = composePost(ctr1, ctr2)
    val inv3 = composeInvariant(ctr1, ctr2, X)

    //Construct a new contract
    val constructor = ctr1.getClass.getConstructors()(0)
    val ctr3 = constructor.newInstance(c3, i3, pre3, post3, inv3, None, None, None).asInstanceOf[C]

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
    //      //... |- preDelta
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

    ctr3.verifyStep(implyR('R) & splitb('R) & andR('R) < (
      splitb('R) & andR('R) < (
        //inv1
        composeb('R) * (5) & choiceb(1, List(1)) & splitb('R) & andR('R) < (
          print("C1;C2") &
          cut(ctr2.sideCondition(ctr1,X)) <(
              //use cut
              print("use cut") partial
            ,
              //show cut

              print("show cut") partial
            )
          ,
          print("C2;C1") partial
          ) partial
        ,
        //inv2
        print("inv2") partial
        ) partial,
      //pre delta
      //TODO does this master() always close, or should I try to reduce the thing further? (how??)
      hideL(-1) & composeb('R) & G & master()
      )
      & print("todo") partial
    )

    //Return verified composite contract
    return ctr3
  }

  def composePorts[C <: Contract](X: Map[Variable, Variable]): Program = {
    X.map(x => Assign(x._1, x._2).asInstanceOf[Program]) match {
      case ass if ass.nonEmpty => ass.reduce((a1, a2) => Compose(a1, a2))
      case _ => Test(True)
    }
  }

  private def composeInvariant[C <: Contract](ctr1: C, ctr2: C, X: Map[Variable, Variable]): And = {
    And(And(ctr1.invariant, ctr2.invariant), preDelta(X))
  }

  private def composePost[C <: Contract](ctr1: C, ctr2: C): And = {
    And(ctr1.post, ctr2.post)
  }

  protected def composePre[C <: Contract](ctr1: C, ctr2: C, X: Map[Variable, Variable]): And = {
    And(And(ctr1.pre, ctr2.pre), preDelta(X))
  }

  def preDelta[C <: Contract](X: Map[Variable, Variable]): BinaryComposite with Formula with Product with Serializable = {
    X.map { case (in, out) => Equal(in, out) }.reduce((a: Formula, b: Formula) => And(a, b))
  }
}
