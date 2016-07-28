package cbcps

import java.util
import java.util.{Locale, Date}
import java.text.DateFormat
import java.text.DateFormat._

/**
 * Created by Andreas on 22.10.2015.
 */
object HelloWorld {

  def main(args: Array[String]) {
    println("Hello world!")
  }
}

object FranceDate {
  def main(args: Array[String]) {
    val now = new util.Date()
    val df = getDateInstance(LONG, Locale.FRANCE)
    println(df format now)
  }
}

object Timer {
  def oncePerSecond(callback: () => Unit): Unit = {
    while (true) {
      callback()
      Thread sleep 1000
    }
  }

  def timeFlies(): Unit = {
    println("Another second has passed!")
  }

  def main(args: Array[String]) {
    oncePerSecond(timeFlies)
  }
}

object TimerAnonymous {
  def oncePerSecond(callback: () => Unit): Unit = {
    while (true) {
      callback()
      Thread sleep 1000
    }
  }

  def main(args: Array[String]) {
    oncePerSecond(() => println("Another anonymous second has passed!"))
  }
}

class Complex(real: Double, imaginary: Double) {
  def re = real

  def im = imaginary

  override def toString() = {
    "" + re + (if (im < 0) "" else "+") + im + "i"
  }
}

object ComplexNumbers {
  def main(args: Array[String]) {
    val c = new Complex(1.2, 3.4)
    println("Real part: " + c.re + ", Imaginary part: " + c.im)
    println(c)
  }
}

abstract class Tree

case class Sum(l: Tree, r: Tree) extends Tree

case class Var(n: String) extends Tree

case class Const(v: Int) extends Tree


object TreeStuff {
  type Environment = String => Int

  def eval(t: Tree, env: Environment): Int = t match {
    case Sum(l, r) => eval(l, env) + eval(r, env)
    case Var(n) => env(n)
    case Const(v) => v
  }

  def derive(t: Tree, v: String): Tree = t match {
    case Sum(l, r) => Sum(derive(l, v), derive(r, v))
    case Var(n) if (n == v) => Const(1)
    case _ => Const(0)
  }

  def main(args: Array[String]) {
    val exp: Tree = Sum(Sum(Var("x"), Var("x")), Sum(Const(7), Var("y")))
    val env: Environment = {
      case "x" => 5
      case "y" => 7
    }
    println("Ausdruck: " + exp)
    println("Auswertung mit x=5, y=7: " + eval(exp, env))
    println("Ableitung von x:\n " + derive(exp, "x"))
    println("Ableitung von y:\n " + derive(exp, "y"))
  }
}

trait Ord {
  def <(that: Any): Boolean

  def <=(that: Any): Boolean = (this < that) || (this == that)

  def >(that: Any): Boolean = !(this <= that)

  def >=(that: Any): Boolean = !(this < that)
}

class MyDate(y: Int, m: Int, d: Int) extends Ord {
  def year = y

  def month = m

  def day = d

  override def toString = year + "-" + month + "-" + day

  override def equals(that: Any): Boolean =
    that.isInstanceOf[MyDate] && {
      val o = that.asInstanceOf[MyDate]
      o.day == day && o.month == month && o.year == year
    }

  def <(that: Any): Boolean = {
    if (!that.isInstanceOf[MyDate])
      sys.error("cannot compare " + that + " and a Date")
    val o = that.asInstanceOf[MyDate]
    (year < o.year) ||
      (year == o.year && (month < o.month ||
        (month == o.month && day < o.day)))
  }
}

object MyDateTest {
  def main(args: Array[String]) {
    def xmas = new MyDate(2015, 12, 24)
    def birthday = new MyDate(2015, 4, 6)

    println("xmas >  birthday? " + (xmas > birthday))
    println("xmas >= birthday? " + (xmas >= birthday))
    println("xmas <  birthday? " + (xmas < birthday))
    println("xmas <= birthday? " + (xmas <= birthday))
    println("xmas =  birthday? " + (xmas == birthday))
    println("xmas != birthday? " + (xmas != birthday))
  }
}

class Reference[T] {
  private var contents: T = _

  def get: T = contents

  def set(value: T) {
    contents = value
  }
}

object IntegerReference{
  def main(args: Array[String]) {
    val cell=new Reference[Int]
    cell.set(42)
    println("Reference contains the answer: "+cell.get)
  }
}