package cbcps


import java.io._

import edu.cmu.cs.ls.keymaerax.core._
import Utility._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

import scala.collection.immutable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.util.{Failure, Success, Try}

/**
  * Created by andim on 22.07.2016.
  */
object Globals {
  private var _vars: Seq[Variable] = Seq(eps)
  private var _prop: Option[Formula] = None
  val t = "t".asVariable
  val t0 = "tOld".asVariable
  val eps = "ep".asVariable


  def addGlobalVariable(v: Variable) = {
    addGlobalVariables(Seq(v))
  }

  def addGlobalVariables(vs: Seq[Variable]) = {
    _vars ++= vs
  }

  def addToGlobalProperty(p: Formula): Boolean = {
    _prop match {
      case None => _prop = Some(p)
      case Some(gp) => _prop = Some(And(gp, p))
    }
    checkGlobalProperty
  }

  private def checkGlobalProperty: Boolean = _prop match {
    case Some(gp) if v(gp).intersect(globalVars).nonEmpty => false
    case _ => true
  }

  def globalVars = _vars ++ Seq(t) ++ Seq(t0)

  def globalProp = _prop match {
    case Some(gp) => gp
    case _ => True
  }

  //TODO initialize t0!
  def initT: Formula = Equal(t, "0".asTerm)

  def initEps: Formula = Greater(eps, "0".asTerm)

  def runT: String = "(" + t.prettyString + "-" + t0.prettyString + ")"

  def oldT: Program = Assign(t0, t)

  def plantT: AtomicODE = AtomicODE(DifferentialSymbol(t), "1".asTerm)

  def evoDomT: Formula = LessEqual(Minus(t,t0), eps)

  def appendGlobalPropertyToFormula(p: Formula): And = {
    _prop match {
      case Some(gp) => return And(p, gp)
      case _ => return And(p, "true".asFormula)
    }
  }

  def save(i: Interface, fName: String) = {
    val stream = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    stream.writeObject(new SerializableGlobals)
    stream.close()
  }

  def load(fName: String): Boolean = {
    Try(new ObjectInputStream(new FileInputStream(new File(fName)))) match {
      case Success(stream) =>
        Try(stream.readObject().asInstanceOf[SerializableGlobals]) match {
          case Success(g) => {
            _vars = g._vars.map(s => s.asVariable)
            _prop = if (g._prop == null) None else Some(g._prop.asFormula)
            stream.close()
            true
          }
          case _ =>
            stream.close()
            false
        }
      case _ => false
    }

  }

  class SerializableGlobals extends Serializable {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)

    def _vars: Seq[String] = Globals._vars.map(v => v.prettyString)

    def _prop: String = Globals._prop match {
      case None => null
      case Some(f) => f.prettyString
    }
  }

}

