package cbcps

import java.io._

import Utility._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}

import scala.collection.immutable._
import scala.collection.mutable
import scala.collection.mutable.LinkedHashMap


/**
  * The interface of a component.
  * Created by andim on 22.07.2016.
  *
  * @param piIn  The set of input variables and respective input properties.
  * @param piOut The set of output variables and respective output properties.
  * @param pre   A set of delta-variables and respective variables to store the previous values.
  */
class Interface(
                 //                vIn: Set[Variable] = Set.empty,
                 val piIn: LinkedHashMap[Variable, Formula] = LinkedHashMap.empty[Variable, Formula],
                 //                vOut: Set[Variable] = Set.empty,
                 val piOut: LinkedHashMap[Variable, Formula] = LinkedHashMap.empty[Variable, Formula],
                 //                vDelta: Set[Variable]= Set.empty,
                 //                vInit: Set[Variable] = Set.empty,
                 val pre: LinkedHashMap[Variable, Variable] = LinkedHashMap.empty[Variable, Variable]
               ) {
  require(vIn.forall(x => (v(x).intersect(vIn ++ vOut).toSet - x).isEmpty),
    "No input formula can mention other input/output variables!")
  require(vIn.intersect(vOut).isEmpty, "" +
    "Input- and output variables must be disjoint!")
  require(vInit.intersect(vIn).isEmpty
    && vInit.intersect(vOut).isEmpty
    && vInit.intersect(vDelta).isEmpty,
    "Initial variables must be pairwise disjoint with input-, output- and delta variables")
  require(Globals.globalVars.intersect(vIn).isEmpty
    && Globals.globalVars.intersect(vOut).isEmpty
    && Globals.globalVars.intersect(vInit).isEmpty
    && Globals.globalVars.intersect(vDelta).isEmpty,
    "Global variables must be pairwise disjoint with input-, output-, delta- and initial variables")

  def vIn: Seq[Variable] = Seq(piIn.keys.toSeq:_*)

  def vOut: Seq[Variable] = Seq(piOut.keys.toSeq:_*)

  def vDelta: Seq[Variable] = Seq(pre.keys.toSeq:_*)

  def vInit: Seq[Variable] = Seq(pre.values.toSeq:_*)

  def piOutAll: Formula = if (piOut.isEmpty) return "true".asFormula else piOut.values.reduce((a, b) => And(a, b))

  def piInAll: Formula = if (piIn.isEmpty) return "true".asFormula else piIn.values.reduce((a, b) => And(a, b))

  override def toString = s"Interface(\npiIn=${piIn.map { case (v, f) => v.prettyString + "->" + f.prettyString }}\npiOut=${piOut.map { case (v, f) => v.prettyString + "->" + f.prettyString }},\npre=${pre.map { case (v1, v2) => v1.prettyString + "->" + v2.prettyString }})"

  def deltaPart: Program = {
    if (pre.isEmpty) {
      "?true;".asProgram
    }
    else {
      pre.map { case (delta, init) => Assign(init, delta) }.reduce((a: Program, b: Program) => Compose(a, b))
    }
  }

  def in: Program = {
    if (piIn.isEmpty) {
      "?true;".asProgram
    }
    else {
      piIn.map { case (v, p) => Compose(AssignAny(v), Test(p)) }.reduce((a: Program, b: Program) => Compose(a, b))
    }
  }

  def variables() = vIn ++ vOut ++ vDelta ++ vInit
}

private class SerializableInterface(i: Interface@transient) extends Serializable {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val _piIn: LinkedHashMap[String, String] = i.piIn.map { case (v: Variable, p: Formula) => (v.prettyString, p.prettyString) }
  val _piOut: LinkedHashMap[String, String] = i.piOut.map { case (v: Variable, p: Formula) => (v.prettyString, p.prettyString) }
  val _pre: LinkedHashMap[String, String] = i.pre.map { case (v1: Variable, v2: Variable) => (v1.prettyString, v2.prettyString) }

  def interface(): Interface = {
    return new Interface(_piIn.map { case (v: String, p: String) => (v.asVariable, p.asFormula) },
      _piOut.map { case (v: String, p: String) => (v.asVariable, p.asFormula) },
      _pre.map { case (v1: String, v2: String) => (v1.asVariable, v2.asVariable) })
  }
}

object Interface {
  def save(i: Interface, fName: String) = {
    val stream = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    stream.writeObject(new SerializableInterface(i))
    stream.close()
  }

  def load(fName: String): Interface = {
    val stream = new ObjectInputStream(new FileInputStream(new File(fName)))
    val ret = stream.readObject().asInstanceOf[SerializableInterface].interface()
    stream.close()
    return ret
  }


  def compose(i1: Interface, i2: Interface, X: mutable.Map[Variable, Variable]) = {
    require((X.keySet -- i1.vIn -- i2.vIn).isEmpty
      && (X.values.toSet -- i1.vOut -- i2.vOut).isEmpty,
      "invalid port mappings in X")
    require(X.forall { case (in: Variable, out: Variable) =>
      (!i1.vIn.contains(in) || !i1.vOut.contains(out)) &&
        (!i2.vIn.contains(in) || !i2.vOut.contains(out))
    },
      "recursive port mappings are not allowed")
    require(X.forall { case (in: Variable, out: Variable) =>
      !(i1.vDelta ++ i2.vDelta).contains(in) || (i1.vDelta ++ i2.vDelta).contains(out)
    },
      "delta inputs must be connected to delta outputs")


    val piIn = LinkedHashMap((i1.piIn ++ i2.piIn).toSeq: _*).filter(a => !X.keySet.contains(a._1))
    val piOut = LinkedHashMap((i1.piOut ++ i2.piOut).toSeq: _*).filter(a => !X.values.toSet.contains(a._1))
    val pre = LinkedHashMap((i1.pre ++ i2.pre).toSeq: _*)

    new Interface(piIn, piOut, pre)
  }

}