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
  * @param piIn  The set of (multi-port) input variables and respective input properties.
  * @param piOut The set of (multi-port) output variables and respective output properties.
  * @param pre   A set of (multi-port) delta-variables and respective variables to store the previous values.
  */
class Interface(
                 val piIn: LinkedHashMap[Seq[Variable], Formula] = LinkedHashMap.empty[Seq[Variable], Formula],
                 val piOut: LinkedHashMap[Seq[Variable], Formula] = LinkedHashMap.empty[Seq[Variable], Formula],
                 val pre: LinkedHashMap[Seq[Variable], Seq[Variable]] = LinkedHashMap.empty[Seq[Variable], Seq[Variable]]
               ) {

  require(piIn.forall { case (xs: Seq[Variable], f: Formula) => (v(f).intersect(vInFlat ++ vOutFlat).toSet -- xs).isEmpty },
    "No input formula can mention other input/output variables!")
  require(vInFlat.intersect(vOutFlat).isEmpty, "" +
    "Input- and output variables must be disjoint!")
  require(vInitFlat.intersect(vInFlat).isEmpty
    && vInitFlat.intersect(vOutFlat).isEmpty
    && vInitFlat.intersect(vDeltaFlat).isEmpty,
    "Initial variables must be pairwise disjoint with input-, output- and delta variables")
  require(Globals.globalVars.intersect(vInFlat).isEmpty
    && Globals.globalVars.intersect(vOutFlat).isEmpty
    && Globals.globalVars.intersect(vInitFlat).isEmpty
    && Globals.globalVars.intersect(vDeltaFlat).isEmpty,
    "Global variables must be pairwise disjoint with input-, output-, delta- and initial variables")

  def vIn: Seq[Seq[Variable]] = Seq(piIn.keys.toSeq: _*)

  def vInFlat: Seq[Variable] = Seq(piIn.keys.flatten.toSeq: _*)

  def vOut: Seq[Seq[Variable]] = Seq(piOut.keys.toSeq: _*)

  def vOutFlat: Seq[Variable] = Seq(piOut.keys.flatten.toSeq: _*)

  def vDelta: Seq[Seq[Variable]] = Seq(pre.keys.toSeq: _*)

  def vDeltaFlat: Seq[Variable] = Seq(pre.keys.flatten.toSeq: _*)

  def vInit: Seq[Seq[Variable]] = Seq(pre.values.toSeq: _*)

  def vInitFlat: Seq[Variable] = Seq(pre.values.flatten.toSeq: _*)

  def piOutAll: Formula = if (piOut.isEmpty) return "true".asFormula else piOut.values.reduce((a, b) => And(a, b))

  def piInAll: Formula = if (piIn.isEmpty) return "true".asFormula else piIn.values.reduce((a, b) => And(a, b))

  override def toString = s"Interface(\npiIn=" +
    piIn.map { case (v, f) => v.map { case s => s.prettyString }.mkString("(", ",", ")") + "->" + f.prettyString } +
    "\npiOut=" + {
    piOut.map { case (v, f) => v.map { case s => s.prettyString }.mkString("(", ",", ")") + "->" + f.prettyString }
  } +
    "\npre=" + {
    pre.map { case (v1, v2) => v1.map { case s => s.prettyString }.mkString("(", ",", ")") + "->" + v2.map { case s => s.prettyString }.mkString("(", ",", ")") }
  }

  def deltaPart: Program = {
    if (pre.isEmpty) {
      "?true;".asProgram
    }
    else {
      pre.map { case (delta: Seq[Variable], init: Seq[Variable]) => MultiPort.assign(init, delta) }.reduce((a: Program, b: Program) => Compose(a, b))
    }
  }

  def in: Program = {
    if (piIn.isEmpty) {
      "?true;".asProgram
    }
    else {
      piIn.map { case (vs, p) => Compose(MultiPort.assignAny(vs), Test(p)) }.reduce((a: Program, b: Program) => Compose(a, b))
    }
  }

  def ports() = vIn ++ vOut

  def variables() = vInFlat ++ vOutFlat ++ vDeltaFlat ++ vInitFlat
}

private class SerializableInterface(i: Interface@transient) extends Serializable {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val _piIn: LinkedHashMap[Seq[String], String] = i.piIn.map { case (vs: Seq[Variable], p: Formula) => (vs.map { case (v: Variable) => v.prettyString }, p.prettyString) }
  val _piOut: LinkedHashMap[Seq[String], String] = i.piOut.map { case (vs: Seq[Variable], p: Formula) => (vs.map { case (v: Variable) => v.prettyString }, p.prettyString) }
  val _pre: LinkedHashMap[Seq[String], Seq[String]] = i.pre.map { case (vs1: Seq[Variable], vs2: Seq[Variable]) => (vs1.map { case (v: Variable) => v.prettyString }, vs2.map { case (v: Variable) => v.prettyString }) }

  def interface(): Interface = {
    return new Interface(_piIn.map { case (vs: Seq[String], p: String) => (vs.map { case (v: String) => v.asVariable }, p.asFormula) },
      _piOut.map { case (vs: Seq[String], p: String) => (vs.map { case (v: String) => v.asVariable }, p.asFormula) },
      _pre.map { case (vs1: Seq[String], vs2: Seq[String]) => (vs1.map { case (v: String) => v.asVariable }, vs2.map { case (v: String) => v.asVariable }) })
  }
}

object Interface {
  /**
    * Constructor for single ports only.
    *
    * @param piIn  The set of input variables and respective input properties.
    * @param piOut The set of output variables and respective output properties.
    * @param pre   A set of delta-variables and respective variables to store the previous values.
    */
  def SinglePortInterface(
                           piIn: LinkedHashMap[Variable, Formula] = LinkedHashMap.empty[Variable, Formula],
                           piOut: LinkedHashMap[Variable, Formula] = LinkedHashMap.empty[Variable, Formula],
                           pre: LinkedHashMap[Variable, Variable] = LinkedHashMap.empty[Variable, Variable]) = {
    new Interface(LinkedHashMap(piIn.map { case (v: Variable, f: Formula) => {
      Seq(v) -> f
    }
    }.toSeq: _*),
      LinkedHashMap(piOut.map { case (v: Variable, f: Formula) => {
        Seq(v) -> f
      }
      }.toSeq: _*),
      LinkedHashMap(pre.map { case (v1: Variable, v2: Variable) => {
        Seq(v1) -> Seq(v2)
      }
      }.toSeq: _*))
  }


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


  //TODO check for single port intersections!
  def compose(i1: Interface, i2: Interface, X: mutable.Map[Seq[Variable], Seq[Variable]]) = {
    require((X.keySet -- i1.vIn -- i2.vIn).isEmpty
      && (X.values.toSet -- i1.vOut -- i2.vOut).isEmpty,
      "invalid port mappings in X")
    require(X.forall { case (in: Seq[Variable], out: Seq[Variable]) =>
      (!i1.vIn.contains(in) || !i1.vOut.contains(out)) &&
        (!i2.vIn.contains(in) || !i2.vOut.contains(out))
    },
      "recursive port mappings are not allowed")
    require(X.forall { case (in: Seq[Variable], out: Seq[Variable]) =>
      !(i1.vDelta ++ i2.vDelta).contains(in) || (i1.vDelta ++ i2.vDelta).contains(out)
    },
      "delta inputs must be connected to delta outputs")


    val piIn = LinkedHashMap((i1.piIn ++ i2.piIn).toSeq: _*).filter(a => !X.keySet.contains(a._1))
    val piOut = LinkedHashMap((i1.piOut ++ i2.piOut).toSeq: _*).filter(a => !X.values.toSet.contains(a._1))
    val pre = LinkedHashMap((i1.pre ++ i2.pre).toSeq: _*)

    new Interface(piIn, piOut, pre)
  }

}

object MultiPort {

  def equals(vs1: Seq[Variable], vs2: Seq[Variable]): Formula = {
    require(vs1.size == vs2.size, "Multiports must have same size")

    if (vs1.isEmpty) {
      "true".asFormula
    }
    else {
      var s: Seq[Formula] = Seq.empty
      (0 until vs1.size) foreach (i => {
        s = s ++ Seq(Equal(vs1(i), vs2(i)))
      })
      s.reduce((a1, a2) => And(a1, a2))
    }
  }

  def assign(vs1: Seq[Variable], vs2: Seq[Variable]): Program = {
    require(vs1.size == vs2.size, "Multiports must have same size")

    if (vs1.isEmpty) {
      Test("true".asFormula)
    }
    else {
      var s: Seq[Program] = Seq.empty
      (0 until vs1.size) foreach (i => {
        s = s ++ Seq(Assign(vs1(i), vs2(i)))
      })
      s.reduce((a1, a2) => Compose(a1, a2))
    }
  }

  def assignAny(vs: Seq[Variable]): Program = {
    if (vs.isEmpty) {
      Test("true".asFormula)
    }
    else {
      var s: Seq[Program] = Seq.empty
      (0 until vs.size) foreach (i => {
        s = s ++ Seq(AssignAny(vs(i)))
      })
      s.reduce((a1, a2) => Compose(a1, a2))
    }
  }

  def multiportAtPosition(ports: Seq[Seq[Variable]], pos: Int): Seq[Variable] = {
    var c = pos
    ports.foreach((vs: Seq[Variable]) => {
      c = c - vs.size
      if (c <= 0)
        return vs
    })
    throw new IllegalArgumentException("No multiport found in '" + ports + "' at position " + pos)
  }
}