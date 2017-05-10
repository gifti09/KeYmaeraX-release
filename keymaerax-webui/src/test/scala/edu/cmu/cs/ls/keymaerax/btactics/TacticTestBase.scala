package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.SQLite.SQLiteDB
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DbProofTree}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.immutable._

/**
 * Base class for tactic tests.
 */
class TacticTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {
  protected var theInterpreter: Interpreter = _

  /** Tests that want to record proofs in a database. */
  class DbTacticTester {
    val user: String = "guest"

    val db: SQLiteDB = {
      val testLocation = File.createTempFile("testdb", ".sqlite")
      val db = new SQLiteDB(testLocation.getAbsolutePath)
      db.cleanup(testLocation.getAbsolutePath)
      db
    }

    /** Creates a new proof entry in the database for a model parsed from `modelContent`. */
    def createProof(modelContent: String, modelName: String = "", proofName: String = "Proof"): Int = {
      db.createModel(user, modelName, modelContent, "", None, None, None, None) match {
        case Some(modelId) => db.createProofForModel(modelId, modelName + proofName, "", "", None)
        case None => fail("Unable to create temporary model in DB")
      }
    }

    /** Prove sequent `s` using tactic  `t`. Record the proof in the database and check that the recorded tactic is
      * the provided tactic. */
    def proveBy(modelContent: String, t: BelleExpr, modelName: String = ""): ProvableSig = {
      val s: Sequent = KeYmaeraXProblemParser(modelContent) match {
        case fml: Formula => Sequent(IndexedSeq(), IndexedSeq(fml))
        case _ => fail("Model content " + modelContent + " cannot be parsed")
      }
      val proofId = createProof(modelContent, modelName)
      val globalProvable = ProvableSig.startProof(s)
      val listener = new TraceRecordingListener(db, proofId, None,
        globalProvable, 0 /* start from single provable */, recursive = false, "custom")
      SequentialInterpreter(listener :: Nil)(t, BelleProvable(ProvableSig.startProof(s))) match {
        case BelleProvable(provable, _) =>
          provable.conclusion shouldBe s
          //extractTactic(proofId) shouldBe t //@todo trim trailing branching nil
          if (provable.isProved) {
            // check that database thinks so too
            val finalTree = DbProofTree(db, proofId.toString)
            finalTree.load()
            //finalTree.leaves shouldBe empty
            finalTree.nodes.foreach(n => n.parent match {
              case None => n.conclusion shouldBe s
              case Some(parent) => n.conclusion shouldBe parent.localProvable.subgoals(n.goalIdx)
            })
          }
          provable
        case r => fail("Unexpected tactic result " + r)
      }
    }

    /** Returns the tactic recorded for the proof `proofId`. */
    def extractTactic(proofId: Int): BelleExpr = DbProofTree(db, proofId.toString).tactic
  }

  /** For tests that want to record proofs in the database. */
  def withDatabase(testcode: DbTacticTester => Any): Unit = testcode(new DbTacticTester())

  /**
   * Creates and initializes Mathematica for tests that want to use QE. Also necessary for tests that use derived
   * axioms that are proved by QE.
   * @example{{{
   *    "My test" should "prove something with Mathematica" in withMathematica { implicit qeTool =>
   *      // ... your test code here
   *    }
   * }}}
   * */
  def withMathematica(testcode: Mathematica => Any) {
    val provider = new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  /**
    * Creates and initializes Z3 for tests that want to use QE. Also necessary for tests that use derived
    * axioms that are proved by QE.
    * Note that Mathematica should also ne initialized in order to perform DiffSolution and CounterExample
    * @example{{{
    *    "My test" should "prove something with Mathematica" in withZ3 { implicit qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withZ3(testcode: Z3 => Any) {
    val provider = new Z3ToolProvider
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  /**
    * Creates and initializes Polya for tests that want to use QE. Also necessary for tests that use derived
    * axioms that are proved by QE.
    * Note that Mathematica should also ne initialized in order to perform DiffSolution and CounterExample
    * @example{{{
    *    "My test" should "prove something with Mathematica" in withPolya { implicit qeTool =>
    *      // ... your test code here
    *    }
    * }}}
    * */
  def withPolya(testcode: Polya => Any) {
    val provider = new PolyaToolProvider
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  /** Test setup */
  override def beforeEach(): Unit = {
    theInterpreter = SequentialInterpreter()
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
    ToolProvider.setProvider(new NoneToolProvider())
  }

  /* Test teardown */
  override def afterEach(): Unit = {
    theInterpreter = null
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    ToolProvider.shutdown()
    ToolProvider.setProvider(new NoneToolProvider())
    TactixLibrary.invGenerator = FixedGenerator(Nil)
  }

  /** Proves a formula using the specified tactic. Fails the test when tactic fails.
    * @todo remove proveBy in favor of [[TactixLibrary.proveBy]] to avoid incompatibilities or meaingless tests if they do something else
    */
  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(fml: Formula, tactic: BelleExpr, labelCheck: Option[List[BelleLabel]]=>Unit = _ => {}): ProvableSig = {
    val v = BelleProvable(ProvableSig.startProof(fml))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, labels) =>
        provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
        labelCheck(labels)
        provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** Proves a sequent using the specified tactic. Fails the test when tactic fails. */
  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(s: Sequent, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(ProvableSig.startProof(s))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  //@deprecated("TactixLibrary.proveBy should probably be used instead of TacticTestBase")
  def proveBy(p: ProvableSig, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(p)
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }

  /** A listener that stores proof steps in the database `db` for proof `proofId`. */
  def listener(db: DBAbstraction)(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int): Seq[IOListener] = {
    val trace = db.getExecutionTrace(proofId, withProvables=false)
    assert(-1 <= parentInTrace && parentInTrace < trace.steps.length, "Invalid trace index " + parentInTrace + ", expected -1<=i<trace.length")
    val parentStep: Option[Int] = if (parentInTrace < 0) None else Some(trace.steps(parentInTrace).stepId)
    val globalProvable = parentStep match {
      case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
      case Some(sId) => db.getExecutionStep(proofId, sId).map(_.local).get
    }
    new TraceRecordingListener(db, proofId, parentStep,
      globalProvable, branch, recursive = false, tacticName) :: Nil
  }

  /** Removes all whitespace for string comparisons in tests.
    * @example{{{
    *     "My string with     whitespace" should equal ("Mystring   with whitespace") (after being whiteSpaceRemoved)
    * }}}
    */
  val whiteSpaceRemoved: Uniformity[String] =
    new AbstractStringUniformity {
      def normalized(s: String): String = s.replaceAll("\\s+", "")
      override def toString: String = "whiteSpaceRemoved"
    }

  def loneSucc(p: ProvableSig): Formula = {
    assert(p.subgoals.length==1)
    assert(p.subgoals.last.succ.length==1)
    p.subgoals.last.succ.last
  }
}