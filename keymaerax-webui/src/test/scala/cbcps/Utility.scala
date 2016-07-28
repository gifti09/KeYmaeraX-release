package cbcps

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.LemmaID
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{And, NamedSymbol, StaticSemantics, SuccPos, _}
import edu.cmu.cs.ls.keymaerax.launcher.{DefaultConfiguration, LemmaDatabaseInitializer}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool, ToolEvidence}
import edu.cmu.cs.ls.keymaerax.tools._
import Utility._

import scala.collection.immutable._
import scala.collection.immutable.Nil
import scala.util.Try


object Utility {

  def v(f: Expression): Set[Variable] =
    StaticSemantics.vars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def fv(f: Expression): Set[Variable] =
    StaticSemantics.freeVars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def bv(f: Formula): Set[Variable] =
    StaticSemantics.boundVars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def bv(f: Program): Set[Variable] =
    StaticSemantics.boundVars(f).toSet[NamedSymbol].map(v => v match {
      case v: Variable => v
      case d: DifferentialSymbol => d.x
      case x => println("Unknown NamedSymbol: " + x); null
    })

  def loadLemma(id: LemmaID): Option[Lemma] = LemmaDBFactory.lemmaDB.get(id)

  def addLemma(lemmaName: String, fact: Provable): Lemma = {
    require(fact.isProved, "only proved Provables would be accepted as lemmas: " + lemmaName + " got\n" + fact)
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(Map("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemma = Lemma(fact, evidence, Some(lemmaName))
    // first check whether the lemma DB already contains identical lemma name
    val lemmaID = if (LemmaDBFactory.lemmaDB.contains(lemmaName)) {
      // identical lemma contents with identical name, so reuse ID
      if (LemmaDBFactory.lemmaDB.get(lemmaName).contains(lemma)) lemma.name.get
      else throw new IllegalStateException("Prover already has a different lemma filed under the same name " + LemmaDBFactory.lemmaDB.get(lemmaName) + " (stored in file name " + lemmaName + ") instnead of " + lemma)
    } else {
      LemmaDBFactory.lemmaDB.add(lemma)
    }
    LemmaDBFactory.lemmaDB.get(lemmaID).get
  }

  def containsLemma(lemmaName: String): Boolean = LemmaDBFactory.lemmaDB.contains(lemmaName)
}

object ProofHelper {
  def initProver = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerate[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p -> inv))
    TactixLibrary.invGenerator = generator

    val mathematica = new Mathematica()
    mathematica.init(DefaultConfiguration.defaultMathematicaConfig)
    DerivedAxioms.qeTool = mathematica
    TactixLibrary.tool = mathematica
  }

  def shutdownProver = {
    if (DerivedAxioms.qeTool != null) {
      DerivedAxioms.qeTool match {
        case t: Tool => t.shutdown()
      }
      DerivedAxioms.qeTool = null
    }
    if (TactixLibrary.tool != null) {
      TactixLibrary.tool match {
        case t: Tool => t.shutdown()
      }
      TactixLibrary.tool = null
      TactixLibrary.invGenerator = new NoneGenerate()
    }
  }

  def verify(goal: Sequent, t: BelleExpr, baseName: Option[String] = None): Option[Lemma] = {
    val p = TactixLibrary.proveBy(goal, t)
    if (p.isProved) {
      if (baseName.isEmpty) {
        Some(null)
      } else {
        val lemmaName = baseName.get
        val t = Try(addLemma(lemmaName, p))
        if (t.isFailure) {
          var i = 1
          var newLemmaName = lemmaName + i
          while (containsLemma(newLemmaName)) {
            i += 1
            newLemmaName = lemmaName + i
          }
          Some(addLemma(newLemmaName, p))
        }
        else {
          Some(t.get)
        }
      }
    }
    else {
      None
    }
  }

  def verify(f: Formula, lemma: Lemma): Boolean = {
    val ret = TactixLibrary.proveBy(f, TactixLibrary.by(lemma))
    if (ret.isProved)
      return true
    else
      return false
  }

  def verify(f: Formula, tactic: BelleExpr): Boolean = verify(f, tactic, None) match {
    case None => false
    case Some(_) => true
  }

  def verify(f: Formula, tactic: BelleExpr, lemmaName: Option[String]): Option[Lemma] = {
    verify(Sequent(IndexedSeq.empty[Formula], IndexedSeq(f)), tactic, lemmaName)
  }

  def verify(s: Sequent, tactic: BelleExpr): Boolean = verify(s, tactic, None) match {
    case None => false
    case Some(_) => true
  }

  //  val helper = new ProvabilityTestHelper((x) => println(x))
  //  private val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
}

