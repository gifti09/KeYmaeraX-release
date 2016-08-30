/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream

/**
 * Parse an axiom string to a list of named formulas that are to be used as axioms in a theory.
 * Created by nfulton on 6/11/15.
 * @author nfulton
 */
object KeYmaeraXAxiomParser extends (String => List[(String,Formula)]) {
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  /**
   * @todo sort checking.
   * @param input The contents of the axiom file.
   * @return A list of named axioms occurring in the file.
   */
  def apply(input: String) : List[(String,Formula)] = {
    val tokens = KeYmaeraXLexer.inMode(input, AxiomFileMode)
    if (DEBUG) println("Tokens are: " + tokens)
    try {
      val (decls, axiomTokens) = KeYmaeraXDeclarationsParser(tokens)
      val axioms = parseAxioms(axiomTokens)
      //@note axiom file does not declare symbols
//      assert(KeYmaeraXParser.LAX || axioms.forall(ax => KeYmaeraXDeclarationsParser.typeAnalysis(decls, ax._2)), "type analysis of axioms")
      axioms
    } catch {case e: ParseException => throw e.inContext("axiom file"/*input*/)}
  }


  /**
   * Very simple -- just read until AXIOM_END.
   * @param input Token string for the axiom file.
   * @return A list of axiom names and the associated formulas.
   */
  def parseAxioms(input: TokenStream): List[(String, Formula)] = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    require(input.head.tok.equals(AXIOM_BEGIN), "expected ALP file to begin with Axion block but found " + input.head)
    val (nextAxiom, nextFormula, remainder) = parseNextAxiom(input)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      List((nextAxiom, nextFormula))
    else
      (nextAxiom, nextFormula) +: parseAxioms(remainder)
  }

  def parseNextAxiom(input: TokenStream): (String, Formula, TokenStream) = {
    require(input.head.tok.equals(AXIOM_BEGIN), "expected ALP file to begin with Axiom block.")
    require(input.tail.head.tok.isInstanceOf[LEMMA_AXIOM_NAME], "expected ALP block to have a string as a name")

    val name = input.tail.head match {
      case Token(LEMMA_AXIOM_NAME(x),_) => x
      case _ => throw new AssertionError("Require should have failed.")
    }
    if (DEBUG) println("Axiom " + name)
    //Find the End. token and exclude it.
    val (axiomTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is AXIOM_BEGIN, 2nd is AXIOM_NAME.

    try {
      val axiom = KeYmaeraXParser.formulaTokenParser(axiomTokens :+ Token(EOF, UnknownLocation))
      (name, axiom, remainderTokens.tail)
    } catch {
      case e: ParseException => throw e.inContext(input.toString, " Error occurred while parsing formula associated with axiom named " + name)
      case e: AssertionError => throw new AssertionError(e.getMessage + " Error occurred while parsing formula associated with axiom named " + name)
    }
  }

}
