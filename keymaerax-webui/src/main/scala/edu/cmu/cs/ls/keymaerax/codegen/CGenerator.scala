/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter


/**
 * Created by ran on 6/16/15.
 * @author Ran Ji
 */
object CGenerator extends CodeGenerator {
  def apply(expr: Expression): String = apply(expr, "long double", Nil, "")
  def apply(expr: Expression, vars: List[Variable]): String = apply(expr, "long double", vars, "")
  def apply(expr: Expression, vars: List[Variable], fileName: String): String = apply(expr, "long double", vars, fileName)
  /** Generate C Code for given expression using the data type cDataType throughout and the input list of variables */
  def apply(expr: Expression, cDataType: String, vars: List[Variable], fileName: String): String = generateCCode(expr, cDataType, vars, fileName)

  /**
   * Generate C code
   *
   * @param expr      KeYmaera X arithmetic expression got from ModelPlex
   * @param cDataType data type
   * @param vars      a list of input variables
   * @param fileName  file name
   * @return          generated C code
   */
  private def generateCCode(expr: Expression, cDataType: String, vars: List[Variable], fileName: String) : String = {
    val names = StaticSemantics.symbols(expr).toList.map(s => nameIdentifier(s))
    require(names.distinct.size == names.size, "Expect unique name_index identifiers for code generation")
    val relevantVars = getRelevantVars(expr, vars)
    if(vars.toSet.diff(relevantVars.toSet).nonEmpty)
      println("[warning] -vars contains unknown variables {" + vars.toSet.diff(relevantVars.toSet).map(v => KeYmaeraXPrettyPrinter(v)).mkString(",") + "}, which will be ignored")
    val calledFuncs = getCalledFuncs(expr, relevantVars)
    val funcHead = "/* monitor */\n" +
      "bool monitor (" + parameterDeclaration(expr, cDataType, relevantVars) + ")"
    val funcBody = compileToC(expr, calledFuncs)
    infoC(fileName) + includeLib + FuncCallDeclaration(calledFuncs, cDataType) + funcHead + " {\n" + "  return " + funcBody + ";" + "\n}\n\n"
    //@note gcc -Wall -Wextra -Werror -std=c99 -pedantic absolutely wants "newline at end of file" -Wnewline-eof
  }

  /** printings for C */
  private def infoC(fileName: String) =
    "/**************************\n" +
      {if(fileName.nonEmpty) "* " + fileName + ".c\n" + "* \n" else "" } +
      " * Generated by KeYmaera X\n" +
      " **************************/\n\n"
  private val includeLib =
    "#include <math.h>\n" +
      "#include <stdbool.h>\n\n"

  /**
   * Generate a list of variables declared as parameters of the main function
   *
   * @param expr      given expression
   * @param cDataType data type
   * @param vars      given list of variables which needs to be declared as parameters,
   *                  if empty, then declare all names in the expression as parameters
   * @return          a lit of parameter declarations
   */
  private def parameterDeclaration(expr: Expression, cDataType: String, vars: List[Variable]) : String = {
    if(vars.isEmpty) {
      StaticSemantics.symbols(expr).toList.sorted.map(
        s => s match {
          case x: Variable => cDataType + " " + nameIdentifier(x)
          case f: Function if f.domain==Unit && f.sort==Real => cDataType + " " + nameIdentifier(f)
        }
      ).mkString(", ")
    } else {
      vars.map(
        v => cDataType + " " + nameIdentifier(v)
      ).mkString(", ")
    }
  }

  /**
   * Get a list of variables relevant to (occur in) the given expression,
   * which includes the post variables that are used as nullary function in the expression
   * and the variable used as a nullary function
   *
   * @param e     expression
   * @param vars  a list of variables
   * @return      a list of variables relevant to e, including post variables and the variables occured as nullary function
   */
  private def getRelevantVars(e: Expression, vars: List[Variable]) : List[Variable] = {
    val allSymbolNames = StaticSemantics.symbols(e).toList
    var relevantVars = List[Variable]()
    for(i <- vars.indices) {
      if(allSymbolNames.contains(vars.apply(i)))
        // variable occurs in the expression, add it to the return list
        relevantVars = vars.apply(i) :: relevantVars
      if((allSymbolNames.contains(Function(nameIdentifier(vars.apply(i)), None, Unit, Real))))
      // variable occur as nullary function, add it to the return list as a variable
        relevantVars = Variable(nameIdentifier(vars.apply(i))) :: relevantVars
      if(allSymbolNames.contains(Variable(nameIdentifier(vars.apply(i))+"post")))
      // post variable occurs in the expression as variable, add it to the return list as a variable
        relevantVars = Variable(nameIdentifier(vars.apply(i))+"post") :: relevantVars
      if(allSymbolNames.contains(Function(nameIdentifier(vars.apply(i))+"post", None, Unit, Real)))
        // post variable occurs in the expression as nullary function, add it to the return list as a variable
        relevantVars = Variable(nameIdentifier(vars.apply(i))+"post") :: relevantVars
    }
    // reverse the list to get the correct order
    relevantVars.reverse
  }

  /**
   * Get a set of names that need to be generated as function calls,
   * by subtracting all relevant names as variables (for the real input variables)
   * and as functions (for post variables and input variables used as nullary functions)
   *
   * @param expr  expression
   * @param vars  a list of variables
   * @return      a set of names that does not occur in relevant variables, thus need to be generated as function calls
   */
  private def getCalledFuncs(expr: Expression, vars: List[Variable]): Set[NamedSymbol] =
    StaticSemantics.symbols(expr).toSet.diff(vars.toSet).diff(vars.map(v => Function(nameIdentifier(v), None, Unit, Real)).toSet)

  /** Declaration of function calls using the list of function call names */
  private def FuncCallDeclaration(calledFuncs: Set[NamedSymbol], cDataType: String): String = {
    if(calledFuncs.nonEmpty) {
      val FuncCallDeclaration = calledFuncs.map(
        s => s match {
          case x: Variable => cDataType + " " + nameIdentifier(x) + "()"
          case f: Function if f.domain==Unit && f.sort==Real => cDataType + " " + nameIdentifier(f) + "()"
        }
      ).mkString("; \n")
      "/* function declaration */\n" + FuncCallDeclaration + ";\n\n"
    } else ""
  }

  /**
   * Compile C code
   *
   * @param e           given expression
   * @param calledFuncs the list of names need to be declared as function calls,
   *                    which helps to determine whether a variable encountered in expression should be generated as a nullary function
   * @return            generated C code
   */
  private def compileToC(e: Expression, calledFuncs: Set[NamedSymbol]) = e match {
    case t : Term => compileTerm(t, calledFuncs)
    case f : Formula => compileFormula(f, calledFuncs)
    case _ => ???
  }


  /** Compile a term to a C expression evaluating it (in the same arithmetic) */
  private def compileTerm(t: Term, calledFuncs: Set[NamedSymbol]) : String = {
    require(t.sort == Real || t.sort == Unit, "can only deal with reals not with sort " + t.sort)
    t match {
      case Neg(c)       => "-" + "(" + compileTerm(c, calledFuncs) + ")"
      case Plus(l, r)   => "(" + compileTerm(l, calledFuncs) + ")" + " + " + "(" + compileTerm(r, calledFuncs) + ")"
      case Minus(l, r)  => "(" + compileTerm(l, calledFuncs) + ")" + " - " + "(" + compileTerm(r, calledFuncs) + ")"
      case Times(l, r)  => "(" + compileTerm(l, calledFuncs) + ")" +  "*"  + "(" + compileTerm(r, calledFuncs) + ")"
      case Divide(l, r) => "(" + compileTerm(l, calledFuncs) + ")" +  "/"  + "(" + compileTerm(r, calledFuncs) + ")"
      case Power(l, r)  => "(" + compilePower(l, r, calledFuncs) + ")"
      // atomic terms
      case Number(n) =>
        assert(n.isValidDouble || n.isValidLong, throw new CodeGenerationException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal-precision numbers"))
        //@note assume the C compiler will detect representation-size errors
        //if(n.toDouble < 0)  "(" + n.underlying().toString + ")"
        //else n.underlying().toString
        //@note with parentheses in case literal is negative
        "(" + n.underlying().toString + ")"
      case t: Variable  =>
        if(!calledFuncs.contains(t)) nameIdentifier(t)
        else nameIdentifier(t)+"()"
      case FuncOf(fn, Nothing) =>
        if(!calledFuncs.contains(fn)) nameIdentifier(fn)
        else nameIdentifier(fn)+"()"
      case FuncOf(fn, child) => nameIdentifier(fn) + "(" + compileTerm(child, calledFuncs) + ")"
      // otherwise exception
      case _ => throw new CodeGenerationException("Conversion of term " + KeYmaeraXPrettyPrinter(t) + " is not defined")
    }
  }

  /** C Identifier corresponding to a NamedSymbol */
  private def nameIdentifier(s: NamedSymbol): String = {
    require(s.isInstanceOf[Function] || s.isInstanceOf[Variable] || s.isInstanceOf[DifferentialSymbol])
    require(s.sort == Real, "only real-valued symbols are currently supported")
    s match {
      case DifferentialSymbol(x) => nameIdentifier(x) + "__p"
      case _ => if (s.index.isEmpty) s.name else s.name + "_" + s.index.get
    }
  }

  /**
   * compile exponentials
   * @param base  base of the exponential
   * @param exp   index of the exponential
   * @return      simplified generation of exponential
   */
  private def compilePower(base: Term, exp: Term, calledFuncs: Set[NamedSymbol]) : String = {
    if(base.equals(Number(0))) {
      //@todo since when is that the case?
      println("[warning] generating 0^0")
      if(exp.equals(Number(0))) "1.0" // 0^0 =1
      else "0.0"  // 0^x = 0
    } else {
      exp match {
        case Number(n) =>
          if(n.isValidInt) {
            // index is integer
            if(n.intValue() == 0) {
              // index is 0, x^0 = 1
              //            assert(!base.equals(Number(0)), throw new CodeGenerationException("Conversion of 0^0 is not defined"))
              "1.0"
            } else if(n.intValue() > 0 ) {
              // index n is a positive integer, expand n times of *
              val ba : String = compileTerm(base, calledFuncs)
              var res : String = "(" + ba + ")"
              for (i <- 1 to n.intValue()-1) {
                res += "*" + "(" + ba + ")"
              }
              res
            } else "1.0/" + "(" + compilePower(base, Number(n.underlying().negate()), calledFuncs) + ")" // index is negative integer
          } else "pow(" + "(" + compileTerm(base, calledFuncs) + ")" + "," + "(" + compileTerm(exp, calledFuncs) + ")" + ")" // index is not integer, use pow function in C
        case Neg(Number(n)) => "1.0/" + "(" + compilePower(base, Number(n), calledFuncs) + ")"  // index is negative
        case _ => "pow(" + "(" + compileTerm(base, calledFuncs) + ")" + "," + "(" + compileTerm(exp, calledFuncs) + ")" + ")"
      }
    }
  }


  /** Compile a formula to a C expression checking it (in the same arithmetic) */
  private def compileFormula(f: Formula, calledFuncs: Set[NamedSymbol]) : String = {
    f match {
      case Not(ff)     => "!" + "(" + compileFormula(ff, calledFuncs) + ")"
      case And(l, r)   => "(" + compileFormula(l, calledFuncs) + ")" + "&&" + "(" + compileFormula(r, calledFuncs) + ")"
      case Or(l, r)    => "(" + compileFormula(l, calledFuncs) + ")" + "||" + "(" + compileFormula(r, calledFuncs) + ")"
      //@todo the following two transformations of formulas should be done by a tactic and just asserted here that these cases no longer happen.
      case Imply(l, r) => compileFormula(Or(Not(l), r), calledFuncs)
      case Equiv(l, r) => compileFormula(And(Imply(l, r), Imply(r, l)), calledFuncs)
        //compileFormula(Or(And(l,r),And(Not(l),Not(r))))
      case Equal(l, r)       => "(" + compileTerm(l, calledFuncs) + ")" + "==" + "(" + compileTerm(r, calledFuncs) + ")"
      case NotEqual(l, r)    => "(" + compileTerm(l, calledFuncs) + ")" + "!=" + "(" + compileTerm(r, calledFuncs) + ")"
      case Greater(l,r)      => "(" + compileTerm(l, calledFuncs) + ")" + ">"  + "(" + compileTerm(r, calledFuncs) + ")"
      case GreaterEqual(l,r) => "(" + compileTerm(l, calledFuncs) + ")" + ">=" + "(" + compileTerm(r, calledFuncs) + ")"
      case Less(l,r)         => "(" + compileTerm(l, calledFuncs) + ")" + "<"  + "(" + compileTerm(r, calledFuncs) + ")"
      case LessEqual(l,r)    => "(" + compileTerm(l, calledFuncs) + ")" + "<=" + "(" + compileTerm(r, calledFuncs) + ")"
      case True              => "true"
      case False             => "false"
      case Box(_, _) | Diamond(_, _) => throw new CodeGenerationException("Conversion of Box or Diamond modality is not allowed")
      case _ => throw new CodeGenerationException("Conversion of formula " + KeYmaeraXPrettyPrinter(f) + " is not defined")
    }
  }
}

