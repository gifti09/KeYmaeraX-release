package cbcps

import java.io._

import edu.cmu.cs.ls.keymaerax.core.{And, AtomicODE, Choice, Compose, DifferentialProduct, ODESystem, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Utility._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}

import scala.collection.mutable._

/**
  * Created by Andreas on 11.11.2015.
  */
class Component(val name: String = "C", val ctrl: Program = "?true;".asProgram, val plant: ODESystem = null, val ports: Program = "?true;".asProgram) {

  require(bv(ctrl).intersect(Globals.globalVars).isEmpty
    && bv(plant).intersect(Globals.globalVars).isEmpty
    && bv(ports).intersect(Globals.globalVars).isEmpty,
    "Global variables must not be bound!")

  //  How to check ctrl does not contain DGL?
  //  assert(,"")

  override def toString = s"Component(name=$name,\nctrl=${ctrl.prettyString},\nplant=${plant.prettyString},\nports=${ports.prettyString})"
}

private class SerializableComponent(c: Component@transient) extends Serializable {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val _name: String = c.name
  val _ctrl: String = c.ctrl.prettyString
  val _plant: String = c.plant.prettyString
  val _ports: String = c.ports.prettyString

  def component(): Component = {
    return new Component(_name, _ctrl.asProgram, _plant.asProgram.asInstanceOf[ODESystem], _ports.asProgram)
  }
}

object Component {

  def save(c: Component, fName: String) = {
    val stream = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    stream.writeObject(new SerializableComponent(c))
    stream.close()
  }

  def load(fName: String): Component = {
    val stream = new ObjectInputStream(new FileInputStream(new File(fName)))
    val ret = stream.readObject().asInstanceOf[SerializableComponent].component()
    stream.close()
    return ret
  }

  /**
    * Compose two components according to the definition from my thesis.
    *
    * @param c1    The first component.
    * @param c2    The second component.
    * @param ports The new ports part of connected ports only. Is composed with the old ports parts internally.
    * @return A new component as the composition of the two received components.
    */
  def compose(c1: Component, c2: Component, ports: Program): Component = {
    new Component(c1.name + "-" + c2.name,
      Choice(Compose(c1.ctrl, c2.ctrl), Compose(c2.ctrl, c1.ctrl)),
      ODESystem(DifferentialProduct(c1.plant.ode, c2.plant.ode), composeDomain(c1, c2)),
      Compose(Compose(c1.ports, c2.ports), ports)
    )
  }

  def composeDomain(c1: Component, c2: Component) = And(c1.plant.constraint, c2.plant.constraint)

  def main(args: Array[String]): Unit = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)

    Globals.addGlobalVariable("A".asVariable)
    print("Global Variables: ")
    Globals.globalVars.foreach(f => print(f.prettyString + ", "))
    println()
    if (Globals.addToGlobalProperty("A>5".asFormula)) {
      println("Global Property: " + Globals.globalProp + " => " + "ok!")
    }
    else {
      println("Global Property: " + Globals.globalProp + " => " + "fail!")
    }
    var c = new Component("Test Component", "out:=0;a:=5;".asProgram, new ODESystem(KeYmaeraXParser.differentialProgramParser("a'=1"), "a<=A".asFormula))
    println("Component: " + c)

    var i = new Interface(LinkedHashMap("in".asVariable -> "in>=0".asFormula), LinkedHashMap("out".asVariable -> "out<A".asFormula), LinkedHashMap("out".asVariable -> "outInit".asVariable))
    println("Interface: " + i)
  }
}
