package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.core.Expression
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser

import scala.util.matching.Regex

private object PSEUDO  extends BelleTerminal("<pseudo>")

sealed abstract class BelleTerminal(val img: String) {
  assert(img != null)

  override def toString = getClass.getSimpleName// + "\"" + img + "\""
  /**
    * @return The regex that identifies this token.
    */
  def regexp : scala.util.matching.Regex = img.r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

private case class IDENT(name: String) extends BelleTerminal(name) {
  assert(name != "US" && name.toLowerCase != "partial")
  override def toString = s"IDENT($name)"
}
private object IDENT {
  def regexp = """([a-zA-Z][a-zA-Z0-9]*)""".r
  //"[\\p{Alpha}\\p{Alnum}]*".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}


// Combinator Tokens
private object SEQ_COMBINATOR extends BelleTerminal("&") {
  override def regexp = "\\&".r
}

private object EITHER_COMBINATOR extends BelleTerminal("|") {
  override def regexp = "\\|".r
}

private object BRANCH_COMBINATOR extends BelleTerminal("<")

private object ON_ALL extends BelleTerminal("OnAll")

private object KLEENE_STAR extends BelleTerminal("*") {
  override def regexp = "\\*".r
}

private object SATURATE extends BelleTerminal("+") {
  override def regexp = "\\+".r
}

private case class N_TIMES(n:Int) extends BelleTerminal(s"^${n}") {
  assert(n >= 0)
  override def toString = s"NTIMES($n)"
}
private object N_TIMES {
  def regexp  = """(\^\d*)""".r
  def startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}


private object US_MATCH extends BelleTerminal("US")

private object RIGHT_ARROW extends BelleTerminal("=>")

// Separation/Grouping Tokens
private object OPEN_PAREN extends BelleTerminal("(") {
  override def regexp = "\\(".r
}
private object CLOSE_PAREN extends BelleTerminal(")") {
  override def regexp = "\\)".r
}
private object COMMA extends BelleTerminal(",")

private trait TACTIC_ARGUMENT

// Positions
private case class ABSOLUTE_POSITION(positionString: String) extends BelleTerminal(positionString) with TACTIC_ARGUMENT {
  override def regexp = ABSOLUTE_POSITION.regexp
  override val startPattern = ABSOLUTE_POSITION.startPattern
  override def toString = s"ABSOLUTE_POSITION($positionString)"
}
private object ABSOLUTE_POSITION {
  def regexp = """(-?\d+(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private object SEARCH_SUCCEDENT extends BelleTerminal("'R") with TACTIC_ARGUMENT
private object SEARCH_ANTECEDENT extends BelleTerminal("'L") with TACTIC_ARGUMENT
private object SEARCH_EVERYWHERE extends BelleTerminal("'-") with TACTIC_ARGUMENT {
  override def regexp = "'\\-".r
}

private object PARTIAL extends BelleTerminal("partial") {
  override def regexp = "(?i)partial".r // allow case-insensitive use of the work partial.
}

/** A dL expression. We allow both terms and formulas as arguments; e.g. in diffGhost. */
private case class EXPRESSION(exprString: String) extends BelleTerminal(exprString) with TACTIC_ARGUMENT {
  val expression: Expression = {
    assert(exprString.startsWith("{`") && exprString.endsWith("`}"),
      s"EXPRESSION.regexp should ensure delimited expression begin and end with {` `}, but an EXPRESSION was constructed with argument: ${exprString}")

    //Remove delimiters and parse the expression.
    KeYmaeraXParser(exprString.drop(2).dropRight(2))
  }

  override def regexp = EXPRESSION.regexp
  override val startPattern = EXPRESSION.startPattern

  override def toString = s"EXPRESSION($exprString)"

  override def equals(other: Any) = other match {
    case EXPRESSION(str) => str == exprString
    case _ => false
  }
}
private object EXPRESSION {
  def regexp = """(\{\`[^\`]*\`\})""".r
  val startPattern = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
/** For testing only. */
object EXPRESSION2 {
  val startPattern = EXPRESSION.startPattern
}

object EOF extends BelleTerminal("<EOF>") {
  override def regexp = "$^".r //none.
}