package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, PosInExpr, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.SequentCalculus._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstractionObj, ProofTree}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Ignore, Matchers}

import scala.collection.immutable._

/** Tests whether execution traces are recorded in the DB in the format expected and with sufficient detail to support
  * the desired operations.
  * Created by bbohrer on 11/23/15.
  */
@Ignore
class TraceRecordingTests extends FlatSpec with Matchers with BeforeAndAfterEach  {
  val db = DBAbstractionObj.testDatabase
  //@todo fill in reasonable data, this is bogus
  private val u = 999
  val listener = new TraceRecordingListener(db, 1337, Some(u), ProvableSig.startProof(True), 0, false, "TODO")
  val theInterpreter = new SequentialInterpreter(Seq(listener))
  object TestLib extends UnifyUSCalculus

  override def beforeEach() = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  private def proveBy(s: Sequent, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable(ProvableSig.startProof(s))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }
  "IOListener" should "Not Crash" in {
    val t1 = System.nanoTime()
    proveBy(Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula)),
        TestLib.useAt("[;] compose", PosInExpr(1 :: Nil))(SuccPos(0))).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula))
    val t2 = System.nanoTime()
    println("My time: " + (t2-t1)/1000000000.0)
    db.printStats()
  }

  /* Same sequent and proof as the mockup for the new proof tree UI. Should give us a good sense of whether this code
  * can support the new UI or not. */
  it should "handle branching proofs" in {
    proveBy(Sequent(IndexedSeq(), IndexedSeq("(z>5) -> ((x < 5) & true) & (2 > y)".asFormula)),
      implyR(SuccPos(0)) & andR(SuccPos(0)))
      db.printStats()
  }

  it should "support multiple proof steps" in {
    val provable =
      proveBy(Sequent(IndexedSeq(), IndexedSeq("(z>5) -> ((x < 5) & true) & (2 > y)".asFormula)),
        implyR(SuccPos(0)))
    proveBy(provable.subgoals.head, andR(SuccPos(0)))
    db.printStats()
  }

  it should "print out some steps for me to check by hand" in {
    println(ProofTree.ofTrace(db.getExecutionTrace(10)))
  }
}
