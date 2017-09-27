package cbcpsold

import java.io._

import cbcps.Utility
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.LemmaID
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Lemma, NamedSymbol, Provable, StaticSemantics, _}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.collection.immutable
import scala.io.Source
import scala.util.Try

/**
 * Created by Andreas on 11.11.2015.
 */
class Component() extends Serializable {
  private var _name: String = "C"
  private var _ctrl: Program = "?true;".asProgram
  private var _plant: ODESystem = null
  private var _vIn: Set[Variable] = Set.empty
  private var _vOut: Set[Variable] = Set.empty
  private var _vLocal: Set[Variable] = Set.empty
  private var _vGlobal: Set[Variable] = Set.empty
  private var _piIn: Map[Variable, Formula] = Map.empty
  private var _piOut: Map[Variable, Formula] = Map.empty

  private var _pre: Formula = True
  private var _post: Formula = True

  private var _lemma: Option[Lemma] = None

  private def lemma_=(x: Option[Lemma]) = {
    _lemma = x
    if (x == None) {
      componentProof = None
    }
  }

  def lemma = _lemma

  def loadLemma(name: String): Boolean = {
    val lemmaDB = LemmaDBFactory.lemmaDB
    val newLemmaID = new LemmaID(name)
    if (lemmaDB.contains(newLemmaID)) {
      val newLemma = lemmaDB.get(newLemmaID).get
      if (verifyContractBy(newLemma, true)) {
        return true
      }
    }
    return false
  }

  def lemmaName: Option[String] = lemma match {
    case s: Some[Lemma] => s.get.name
    case None => None
  }

  private var componentProof: Option[ComponentProof] = None

  def proof: Option[ProvableSig] = if (lemma.isEmpty) None else Some(lemma.get.fact)

  def name = _name

  def name_=(x: String): Unit = _name = x

  def ctrl = _ctrl

  def ctrl_=(x: Program): Unit = {
    _ctrl = x
    lemma = None
  }

  def plant = _plant match {
    case null => ODESystem(Component.dt)
    case x: ODESystem => ODESystem(DifferentialProduct(Component.dt, x.ode), x.constraint)
  }

  private def countDG(dg: DifferentialProgram): Integer = dg match {
    case p: DifferentialProduct => countDG(p.left) + countDG(p.right)
    case s: ODESystem => countDG(s.ode)
    case a: AtomicODE => 1
  }

  def countDG: Integer = countDG(_plant.ode)

  def plantNoTime = _plant

  def plant_=(x: ODESystem): Unit = {
    _plant = x
    lemma = None
  }

  def vIn = _vIn

  def vIn_=(x: Set[Variable]): Unit = {
    _vIn = x
    lemma = None
  }

  def vOut = _vOut

  def vOut_=(x: Set[Variable]): Unit = {
    _vOut = x
    lemma = None
  }


  def vLocal = _vLocal

  def vLocal_=(x: Set[Variable]): Unit = {
    _vLocal = x
    lemma = None
  }


  def vGlobal = _vGlobal

  def vGlobal_=(x: Set[Variable]): Unit = {
    _vGlobal = x
    lemma = None
  }


  def piIn = _piIn

  def piIn_=(x: Map[Variable, Formula]): Unit = {
    _piIn = x
    lemma = None
  }

  def piOut = _piOut

  def piOut_=(x: Map[Variable, Formula]): Unit = {
    _piOut = x
    lemma = None
  }

  def vars = vIn ++ vOut ++ vLocal ++ vGlobal ++ Seq(Component.t)

  def input: Program = piIn.map(x => Compose(AssignAny(x._1), Test(x._2))) match {
    case inputProperties if inputProperties.nonEmpty => inputProperties.reduce((a: Compose, b: Compose) => Compose(a, b))
    case _ => Test(True)
  }

  def hp = Component.hp(this)

  def pre = _pre

  def pre_=(x: Formula): Unit = {
    _pre = x
    lemma = None
  }

  def post = _post

  def post_=(x: Formula): Unit = {
    _post = x
    lemma = None
  }

  def contract = Component.contract(hp, pre, post, piOut)

  def isValid(): Boolean = {
    return getInvalidMessage() == ""
  }

  def getInvalidMessage(): String = {
    val tryBvCtrl = Try(StaticSemantics(ctrl).bv.toSet[NamedSymbol].filter(v => !v.isInstanceOf[DifferentialSymbol]))
    val tryBvPlant = Try(StaticSemantics(plant).bv.toSet[NamedSymbol].filter(v => !v.isInstanceOf[DifferentialSymbol]))
    val tryFvCtrl = Try(StaticSemantics(ctrl).fv.toSet[NamedSymbol].filter(v => !v.isInstanceOf[DifferentialSymbol]))
    val tryFvPlant = Try(StaticSemantics(plant).fv.toSet[NamedSymbol].filter(v => !v.isInstanceOf[DifferentialSymbol]))

    if (tryBvCtrl.isFailure) {
      return "could not extract bound variables for 'ctrl'\n" + tryBvCtrl.failed.get.getMessage
    }
    if (tryBvPlant.isFailure) {
      return "could not extract bound variables for 'plant'\n" + tryBvPlant.failed.get.getMessage
    }
    if (tryFvCtrl.isFailure) {
      return "could not extract free variables for 'ctrl'\n" + tryFvCtrl.failed.get.getMessage
    }
    if (tryFvPlant.isFailure) {
      return "could not extract free variables for 'plant'\n" + tryFvPlant.failed.get.getMessage
    }


    val bvCtrlProg = tryBvCtrl.get
    val bvPlantProg = tryBvPlant.get - Component.t
    val fvCtrlProg = tryFvCtrl.get
    val fvPlantProg = tryBvPlant.get

    //(Vin CUP Vglobal) CAP (BV(ctrl) CUP BV(plant)) = 0
    if (!(bvCtrlProg ++ bvPlantProg).intersect((vIn.toSet ++ vGlobal.toSet)).isEmpty) {
      return "(Vin CUP Vglobal) CAP (BV(ctrl) CUP BV(plant)) != 0"
    }
    //time is not bound in (user-)plant or control
    if ((bvCtrlProg ++ bvPlantProg).contains(Component.t)) {
      return "time is bound in (user-)plant or control"
    }
    //no input predicate mentions other input variables
    piIn.foreach(
      (x: (Variable, Formula)) => {
        if (StaticSemantics(x._2).fv.toSet[NamedSymbol].intersect(vIn.toSet) != Set(x._1)) {
          return "input predicate for '" + x._1.prettyString + "' mentions other input variables: " + x._2.prettyString
        }
      }
    )
    //is there an input property for each input variable and vice-versa
    if (!vIn.sameElements(piIn.keySet.toSeq)) {
      return "not every input variable has an input property"
    }
    //is there an output property for each output variable and vice-versa
    if (!vOut.sameElements(piOut.keySet.toSeq)) {
      return "not every output variable has an output property"
    }
    //component can only use known variables
    if (((bvCtrlProg ++ bvPlantProg ++ fvCtrlProg ++ fvPlantProg + Component.t) -- vars).nonEmpty) {
      return "component uses undefined variables"
    }

    //everything is fine
    ""
  }

  def isVerified(): Boolean = {
    proof.isDefined && proof.get.isProved
  }

  def verifyContractBy(l: Lemma, keep: Boolean): Boolean = verifyContract(TactixLibrary.by(l)) match {
    case a: Some[Lemma] => {
      if (keep)
        lemma = a
      true
    }
    case None => false
  }

  def verifyContractBy(cp: ComponentProof, keep: Boolean): Boolean = verifyContract(ComponentProof.getTactic(cp)) match {
    case a: Some[Lemma] => {
      if (keep) {
        lemma = a
        componentProof = Some(cp)
      }
      true
    }
    case None => false
  }

  private def verifyContract(tactic: BelleExpr): Option[Lemma] = {
    if (isValid() && !isVerified() && contract != "") {
      val ret = TactixLibrary.proveBy(contract, tactic)

      if (ret.isProved) {
        var lemmaName = "Lemma Proof " + name
        val evidence = ToolEvidence(immutable.List("input" -> ret.toString, "output" -> "true")) :: Nil
        //proved, so keep lemma and save lemma to LemmaDB
        val lemmaDB = LemmaDBFactory.lemmaDB
        var i = 1
        while (lemmaDB.contains(new LemmaID(lemmaName))) {
          lemmaName = "Lemma Proof " + name + "-" + i
          i += 1
        }
        val l = Some(Lemma(ret, evidence, Some(lemmaName)))
        //lemmaDB.add(l.get)
        return l
      }
    }
    return None
  }

  def proofGoals(invariant: Formula): IndexedSeq[Sequent] = {
    val rootNode = new Sequent(immutable.IndexedSeq.empty[Formula], immutable.IndexedSeq(contract))
    val p=TactixLibrary.proveBy(rootNode,implyR(1) & I(invariant)(1))
    p.subgoals

//    p.subgoals.foreach(
//      a => a.tacticInfo.infos.get("branchLabel") match {
//        case Some(l: String) => ret = ret + (l -> (a.sequent match {
//          case b if b.ante.isEmpty => b
//          case b => TactixLibrary.proveBy(b, ComponentProof.preTactic).subgoals(0)
//        }))
//        case None => Nil
//      }
//    )
//
//    ret
  }

  override def toString = s"Component(name=$name,\nctrl=${ctrl.prettyString},\nplant=${plant.prettyString},\nvIn=${vIn.map(a => a.prettyString)}, vOut=${vOut.map(a => a.prettyString)}, vLocal=${vLocal.map(a => a.prettyString)}, vGlobal=${vGlobal.map(a => a.prettyString)},\npiIn=${piIn.map(a => a._1.prettyString + "->" + a._2.prettyString)}, piOut=${piOut.map(a => a._1.prettyString + "->" + a._2.prettyString)},\npre=${pre.prettyString}, post=${post.prettyString},\nisValid=$isValid(), isVerified=$isVerified())"
}

object Component {
  val t = "tt".asVariable
  val dt = AtomicODE(DifferentialSymbol(Component.t), "1.1".asTerm)
  val P_FILE_POSTFIX = "f"
  val P_NAME = "-name"
  val P_CTRL = "-ctrl"
  val P_CTRL_FILE = P_CTRL + P_FILE_POSTFIX
  val P_PLANT = "-plant"
  val P_PLANT_FILE = P_PLANT + P_FILE_POSTFIX
  val P_PRE = "-pre"
  val P_PRE_FILE = P_PRE + P_FILE_POSTFIX
  val P_POST = "-post"
  val P_POST_FILE = P_POST + P_FILE_POSTFIX
  val P_PIN = "-pIn"
  val P_PIN_FILE = P_PIN + P_FILE_POSTFIX
  val P_POUT = "-pOut"
  val P_POUT_FILE = P_POUT + P_FILE_POSTFIX
  val P_VIN = "-vIn"
  val P_VIN_FILE = P_VIN + P_FILE_POSTFIX
  val P_VOUT = "-vOut"
  val P_VOUT_FILE = P_VOUT + P_FILE_POSTFIX
  val P_VLOCAL = "-vLocal"
  val P_VLOCAL_FILE = P_VLOCAL + P_FILE_POSTFIX
  val P_VGLOBAL = "-vGlobal"
  val P_VGLOBAL_FILE = P_VGLOBAL + P_FILE_POSTFIX

  def parseComponent(c: Component, list: List[String]): Component = {
    def isSwitch(s: String) = s(0) == '-'
    var content: String = ""

    list match {
      case Nil => c
      case P_NAME :: value :: tail =>
        c.name = value
        parseComponent(c, tail)
      case P_CTRL :: value :: tail =>
        c.ctrl = value.asProgram
        parseComponent(c, tail)
      case P_CTRL_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.ctrl = content.asProgram
        parseComponent(c, tail)
      case P_PLANT :: value :: tail =>
        c.plant = value.asProgram match {
          case a: ODESystem => a
          case _ => println("Error parsing plant!")
            null
        }
        parseComponent(c, tail)
      case P_PLANT_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.plant = content.asProgram match {
          case a: ODESystem => a
          case _ => println("Error parsing plant!")
            null
        }
        parseComponent(c, tail)
      case P_PRE :: value :: tail =>
        c.pre = value.asFormula
        parseComponent(c, tail)
      case P_PRE_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.pre = content.asFormula
        parseComponent(c, tail)
      case P_POST :: value :: tail =>
        c.post = value.asFormula
        parseComponent(c, tail)
      case P_POST_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.post = content.asFormula
        parseComponent(c, tail)
      case P_PIN :: value :: tail =>
        def matchVarPred(s: List[String], map: Map[Variable, Formula]): Map[Variable, Formula] = {
          s match {
            case Nil => map
            case v :: p :: tail =>
              matchVarPred(tail, map ++ Map(v.asVariable -> p.asFormula))
            case _ => println("Error parsing piIn!")
              null
          }
        }
        c.piIn = matchVarPred(value.split(",").toList, Map())
        parseComponent(c, tail)
      case P_PIN_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        def matchVarPred(s: List[String], map: Map[Variable, Formula]): Map[Variable, Formula] = {
          s match {
            case Nil => map
            case v :: p :: tail =>
              matchVarPred(tail, map ++ Map(v.asVariable -> p.asFormula))
            case _ => println("Error parsing piIn!")
              null
          }
        }
        c.piIn = matchVarPred(content.split(",").toList, Map())
        parseComponent(c, tail)
      case P_POUT :: value :: tail =>
        def matchVarPred(s: List[String], map: Map[Variable, Formula]): Map[Variable, Formula] = {
          s match {
            case Nil => map
            case v :: p :: tail =>
              matchVarPred(tail, map ++ Map(v.asVariable -> p.asFormula))
            case _ => println("Error parsing piOut!")
              null
          }
        }
        c.piOut = matchVarPred(value.split(",").toList, Map())
        parseComponent(c, tail)
      case P_POUT_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        def matchVarPred(s: List[String], map: Map[Variable, Formula]): Map[Variable, Formula] = {
          s match {
            case Nil => map
            case v :: p :: tail =>
              matchVarPred(tail, map ++ Map(v.asVariable -> p.asFormula))
            case _ => println("Error parsing piOut!")
              null
          }
        }
        c.piOut = matchVarPred(content.split(",").toList, Map())
        parseComponent(c, tail)
      case P_VLOCAL :: value :: tail =>
        c.vLocal = value.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VLOCAL_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.vLocal = content.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VGLOBAL :: value :: tail =>
        c.vGlobal = value.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VGLOBAL_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.vGlobal = content.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VIN :: value :: tail =>
        c.vIn = value.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VIN_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.vIn = content.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VOUT :: value :: tail =>
        c.vOut = value.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case P_VOUT_FILE :: value :: tail =>
        content = Source.fromFile(value).mkString
        c.vOut = content.split(",").toSet[String].map(_.asVariable)
        parseComponent(c, tail)
      case option :: tail if isSwitch(option) =>
        println("Unknown option " + option)
        null
      case anything :: tail =>
        println("Unknown parameter " + anything)
        null
    }
  }

  /**
   * Load Component from Text-File
   * @deprecated
   * @param fName
   * @return
   */
  def loadComponent(fName: String): Option[Component] = {
    try {
      var c: Component = null
      val s = Source.fromFile(fName).mkString

      var pre: Formula = null
      var ctrl: Program = null
      var plant: ODESystem = null

      s.split('.').toList match {
        case contract :: vlocal :: vglobal :: vin :: vout :: lemma => {
          contract.asFormula match {
            case Imply(pre, Box(Loop(Compose(ctrl, plant: ODESystem)), post: Formula)) => {
              c.ctrl = ctrl
              c.plant = plant
              c.pre = pre
              c.post = post
            }
            case _ => return None
          }
          c.vLocal = vlocal.split(",").toSet[String].map(_.asVariable)
          c.vGlobal = vglobal.split(",").toSet[String].map(_.asVariable)
          c.vIn = vin.split(",").toSet[String].map(_.asVariable)
          c.vOut = vout.split(",").toSet[String].map(_.asVariable)
        }
        case _ => return None
      }
      println(c)
      Some(c)
    }
    catch {
      case e => {
        e.printStackTrace()
        None
      }
    }
  }

  /**
   * Save Component as Text-File
   * @deprecated
   * @param c
   * @param fName
   * @return
   */
  def saveComponent(c: Component, fName: String): Boolean = {
    try {
      PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
      val file = new File(fName)
      val writer = new PrintWriter(new FileWriter(file))
      writer.print(c.contract.prettyString)
      writer.print(".")
      writer.print(c.vLocal.mkString(","))
      writer.print(".")
      writer.print(c.vGlobal.mkString(","))
      writer.print(".")
      writer.print(c.vIn.mkString(","))
      writer.print(".")
      writer.print(c.vOut.mkString(","))
      if (c.isVerified()) {
        writer.print(".")
        writer.print(c.lemmaName.get)
      }
      writer.close()
    }
    catch {
      case e => {
        e.printStackTrace()
        false
      }
    }
    //everything went fine
    true
  }

  def saveComponentAsList(c: Component, fName: String): Boolean = {
    try {
      val file = new File(fName)
      val stream = new ObjectOutputStream(new FileOutputStream(file))
      var l: List[String] = List.empty
      l = l ++ List(P_NAME, c.name)
      l = l ++ List(P_CTRL, c.ctrl.prettyString)
      if (c.plantNoTime != null) l = l ++ List(P_PLANT, c.plantNoTime.prettyString)
      l = l ++ List(P_PRE, c.pre.prettyString)
      l = l ++ List(P_POST, c.post.prettyString)
      if (c.vIn.nonEmpty) l = l ++ List(P_VIN, c.vIn.map(a => a.prettyString).mkString(","))
      if (c.vOut.nonEmpty) l = l ++ List(P_VOUT, c.vOut.map(a => a.prettyString) mkString (","))
      if (c.vLocal.nonEmpty) l = l ++ List(P_VLOCAL, c.vLocal.map(a => a.prettyString) mkString (","))
      if (c.vGlobal.nonEmpty) l = l ++ List(P_VGLOBAL, c.vGlobal.map(a => a.prettyString) mkString (","))
      if (c.piIn.nonEmpty) l = l ++ List(P_PIN, c.piIn.map(a => a._1.prettyString + "," + a._2.prettyString).mkString(","))
      if (c.piOut.nonEmpty) l = l ++ List(P_POUT, c.piOut.map(a => a._1.prettyString + "," + a._2.prettyString).mkString(","))
      println("Saving List: " + l)
      stream.writeObject(l)
      stream.flush()
      c.lemmaName match {
        case lemmaName: Some[String] => stream.writeUTF(lemmaName.get)
        case _ =>
      }
      stream.close()
    }
    catch {
      case e => {
        e.printStackTrace()
        false
      }
    }
    //everything went fine
    true
  }

  def loadComponentAsList(fName: String): Option[Component] = {
    try {
      val stream = new ObjectInputStream(new FileInputStream(new File(fName)))
      val list = stream.readObject().asInstanceOf[List[String]]
      val lemmaName = if (stream.available() > 0) stream.readUTF() else null
      stream.close()
      val c = parseComponent(new Component(), list)
      if (c != null) {
        if (lemmaName != null)
          c.loadLemma(lemmaName)
        Some(c)
      }
      else
        None
    }
    catch {
      case e => {
        e.printStackTrace()
        None
      }
    }
  }

  def contract(hp: Program, pre: Formula, post: Formula, piOut: Map[Variable, Formula]): Formula = {
    Imply(pre, Box(hp, piOut.values.foldLeft(post)((a, b) => And(a, b))))
  }

  //    "(" + Component.t + "=0&" + pre + ")->" + hp + "(" + post + (if (!piOut.isEmpty) "&" + piOut.values.mkString("&") else "") + ")"

  def hp(c: Component): Program = {
    Loop(Compose(Compose(c.input, c.ctrl), c.plant))
  }

  //TODO maybe should not return "null", but "?true" if there are no ports
  def ports(c: Component, X: Map[Variable, Variable]): Program = {
    val ass = X.filter(x => c.vIn.contains(x._1)).map(x => Assign(x._1, x._2))
    val ports: Program = if (ass.size > 1) ass.fold(ass.head.asInstanceOf[Program])((a: Program, b: Program) => Compose(a, b)) else if (ass.size == 1) ass.last else null
    ports
  }

  def compatibilityProofObligation(c1: Component, c2: Component, X: Map[Variable, Variable]): Option[Formula] = {
    try {
      if (!X.keySet.subsetOf(c1.vIn ++ c2.vIn) || !X.values.toSet.subsetOf(c1.vOut ++ c2.vOut)) {
        println("Invalid Port Mapping!")
        return None
      }
      val m1 = X.filter(a => c1.vIn.contains(a._1)).map(a => {
        ("[" + a._1.prettyString + ":=" + a._2.prettyString + ";](" + c2.piOut(a._2).prettyString + "->" + c1.piIn(a._1).prettyString + ")")
      })
      val m2 = X.filter(a => c2.vIn.contains(a._1)).map(a => {
        ("[" + a._1.prettyString + ":=" + a._2.prettyString + ";](" + c1.piOut(a._2).prettyString + "->" + c2.piIn(a._1).prettyString + ")")
      })
      val f = if (m1.isEmpty & m2.isEmpty) True else (m1.toSet ++ m2.toSet).mkString("(", ")&(", ")").asFormula
      Some(f)
    }
    catch {
      case e => e.printStackTrace(); None
    }
  }

//  def verifyComposite(c1: Component, c2: Component, X: Map[Variable, Variable], cpoLemma: Lemma): Option[Lemma] = {
//    //check if c1 and c2 are valid and verified
//    if (!c1.isVerified() && !c2.isVerified()) {
//      println("Error verifying composite: c1 and/or c2 not verified!")
//      return None
//    }
//
//    //check if given lemma verifies cpo
//    require(ProofHelper.verify(compatibilityProofObligation(c1, c2, X).get, cpoLemma).isDefined, "Compatibility Proof Obligation could not be verified!")
//
//    val c3: Component = compose(c1, c2, X)
//
//    val cp3 = ComponentProof(And(c1.componentProof.get.invariant, c2.componentProof.get.invariant))
//    val pg3 = c3.proofGoals(cp3.invariant)
//    pg3.foreach(x => x match { /* TODO labels gibts nimma! */
//      case (n: String, s: Sequent) if (n == indInitLbl) =>
//        cp3.indInit = ProofHelper.verify(s, debug("<< INIT COMPOSITE >>") & implyR(1) && ls(andR) &&(la(andL) & hideL(-2) & PropositionalTacticsImpl.InverseImplyRightT() & TactixLibrary.by(c1.componentProof.get.indInit), la(andL) & hideL(-1) & PropositionalTacticsImpl.InverseImplyRightT() & TactixLibrary.by(c2.componentProof.get.indInit)), "C3-init").getOrElse(null)
//      case (n: String, s: Sequent) if (n == indUseCaseLbl) =>
//        cp3.indUseCase = ProofHelper.verify(s, debug("<< USECASE COMPOSITE >>") & ls(implyR) & la(andL) & ls(andR) &&(hideL(-2) & cut(c1.componentProof.get.indUseCase.fact.conclusion.succ(0)) & onBranch((cutShowLbl, hideL(-1) & hideR(1) & TactixLibrary.by(c1.componentProof.get.indUseCase)), (cutUseLbl, prop)), hideL(-1) & cut(c2.componentProof.get.indUseCase.fact.conclusion.succ(0)) & onBranch((cutShowLbl, hideL(-1) & hideR(1) & TactixLibrary.by(c2.componentProof.get.indUseCase)), (cutUseLbl, prop))), "C3-usecase").getOrElse(null)
//      case (n: String, s: Sequent) if (n == indStepLbl) =>
//        cp3.indStep = ProofHelper.verify(s, debug("<< STEP COMPOSITE >>") & ls(implyR) & la(andL) & useAt("[] split")(1) & andR(1) &&(
//          debug("#1") &
//            cut(Box(Compose(Compose(c3.input, c3.ctrl), c1.plant), c1.componentProof.get.invariant)) & onBranch(
//            //lemma 2 -> cut use closes!
//            (cutUseLbl, hideL(-1) & hideL(-1) & composeb(-1) & composeb(1) & AxiomaticRuleTactics.boxMonotoneT & Lemmas.lemma2(1, c1.countDG, c2.countDG, false) & prop),
//            //continued
//            (cutShowLbl, hideR(1) & composeb(1) & composeb(1) & choiceb(1, 1 :: Nil) & splitb(1) & andR(1) &&
//              (
//                debug("#3") &
//                  //compose
//                  composeb(1, 1 :: Nil) &
//                  //dropCtrl
//                  cut(Box(c3.input, Box(if (Component.ports(c1, X) != null) Compose(Component.ports(c1, X), c1.ctrl) else c1.ctrl, Box(c1.plant, c1.componentProof.get.invariant)))) & onBranch(
//                  //lemma 1 -> cut use closes!
//                  (cutUseLbl, hide(-1) & hide(-1) & AxiomaticRuleTactics.boxMonotoneT & AxiomaticRuleTactics.boxMonotoneT & Lemmas.lemma1BA(1)),
//                  //continued
//                  (cutShowLbl,
//                    //assOrd...
//                    debug("go on"))),
//                debug("#3/2")
//                )
//              )
//          ),
//          debug("#2") &
//            cut(Box(Compose(Compose(c3.input, c3.ctrl), c2.plant), c2.componentProof.get.invariant)) & onBranch(
//            //lemma 2 -> cut use closes!
//            (cutUseLbl, hideL(-1) & hideL(-1) & composeb(-1) & composeb(1) & TactixLibrary.monb & Lemmas.lemma2(1, 0, c1.countDG, true) & prop),
//            //continued
//            (cutShowLbl, hideR(1))
//          )), "C3-step").getOrElse(null)
//      case (n: String, _) => require(false, "Unexpected proof goal '" + n + "'!")
//    })
//
//    println("cp3 isComplete? " + cp3.isComplete)
//    if (cp3.isComplete) c3.verifyContractBy(cp3, true)
//    println("verified? " + c3.isVerified)
//
//    val tactic = ls(implyR) /*& ls(I(new And(c1.componentProof.get.invariant, c2.componentProof.get.invariant))) & onBranch(
//      (indInitLbl, debug("Init") & ls(andR) &&((la(andL) *) & TactixLibrary.by(c1.componentProof.get.indInit), (la(andL) *) & TactixLibrary.by(c2.componentProof.get.indInit))),
//      (indUseCaseLbl, debug("Use Case") & ls(implyR) & ls(andR) &&((la(andL) *) & TactixLibrary.by(c1.componentProof.get.indUseCase), (la(andL) *) & TactixLibrary.by(c2.componentProof.get.indUseCase))),
//      (indStepLbl, debug("Step") & ls(implyR) & (la(andL) *) & ls(composeb) & ls(andR) &&(debug("Lemma 2"), debug("Lemma 2")))
//    )*/
//
//    ProofHelper.verify(c3.contract, tactic, "Lemma Proof " + c3.name)
//  }

  def compose(c1: Component, c2: Component, X: Map[Variable, Variable]): Component = {
    val c3 = new Component

    val ports1 = Component.ports(c1, X)
    val ports2 = Component.ports(c2, X)

    //ctrl
    c3.ctrl = Choice(Compose((if (ports1 == null) c1.ctrl else Compose(ports1, c1.ctrl)), (if (ports2 == null) c2.ctrl else Compose(ports2, c2.ctrl))),
      Compose((if (ports2 == null) c2.ctrl else Compose(ports2, c2.ctrl)), (if (ports1 == null) c1.ctrl else Compose(ports1, c1.ctrl))))

    //plant
    c3.plant = ODESystem(DifferentialProduct(c1.plantNoTime.ode, c2.plantNoTime.ode), And(c1.plantNoTime.constraint, c2.plantNoTime.constraint))

    //pre + post
    c3.pre = And(c1.pre, c2.pre)
    c3.post = And(c1.post, c2.post)

    //vars
    c3.vGlobal = c1.vGlobal ++ c2.vGlobal
    c3.vIn = (c1.vIn ++ c2.vIn) -- X.keySet
    c3.vOut = (c1.vOut ++ c2.vOut) -- X.values.toSet
    c3.vLocal = c1.vLocal ++ c2.vLocal ++ X.keySet ++ X.values.toSet

    //piIn + piOut
    c3.piIn = (c1.piIn ++ c2.piIn).filter(a => !X.keySet.contains(a._1))
    c3.piOut = (c1.piOut ++ c2.piOut).filter(a => !X.values.toSet.contains(a._1))

    //name
    c3.name = c1.name + "||" + c2.name

    c3
  }
}