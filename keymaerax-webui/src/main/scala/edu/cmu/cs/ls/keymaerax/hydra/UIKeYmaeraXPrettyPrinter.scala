/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXWeightedPrettyPrinter
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.OpSpec.op

object UIKeYmaeraXPrettyPrinter {
  /** UIKeYmaeraXPrettyPrinter(topId) is a UI pretty printer for sequent-formula with identifier topId */
  def apply(topId: String, plainText: Boolean): Expression=>String = new UIKeYmaeraXPrettyPrinter(topId, plainText)
}

/**
  * User-interface pretty printer for KeYmaera X syntax.
  * @author Andre Platzer
  */
class UIKeYmaeraXPrettyPrinter(val topId: String, val plainText: Boolean) extends KeYmaeraXWeightedPrettyPrinter {
  private val HTML_OPEN = "$#@@$"
  private val HTML_CLOSE = "$@@#$"

  override def apply(expr: Expression): String = stringify(expr)
    //@todo custom OpSpec?
    .replaceAllLiterally("&", "&#8743;")
    .replaceAllLiterally("!", "&not;")
    .replaceAllLiterally("|", "&#8744;")
    .replaceAllLiterally("->", "→")
    .replaceAllLiterally("<->", "&#8596;")
    .replaceAllLiterally("<=", "&leq;")
    .replaceAllLiterally("!=", "&ne;")
    .replaceAllLiterally(">=", "&geq;")
    //.replaceAllLiterally("*", "&middot;") // program * vs. multiplication *
    // ^y --> <sup>y</sup>
    .replaceAllLiterally("\\forall", "&forall;")
    .replaceAllLiterally("\\exists", "&exist;")
    .replaceAllLiterally("[", "&#91;")
    .replaceAllLiterally("]", "&#93;")
    .replaceAllLiterally("++", "&#8746;")
    .replaceAllLiterally("<", "&lt;")
    .replaceAllLiterally(">", "&gt;")
    .replaceAllLiterally(HTML_OPEN, "<")
    .replaceAllLiterally(HTML_CLOSE, ">")

  protected override def emit(q: PosInExpr, s: String): String = wrap(topId + "," + q.pos.mkString(","), s)

//  private def wrap(id: String, content: String): String =
//    HTML_OPEN + "term id=\"" + id + "\"" + HTML_CLOSE + content + HTML_OPEN + "/term" + HTML_CLOSE

  private def wrap(id: String, content: String): String =
    if (plainText) content
    else s"""${HTML_OPEN}span ng-class="{'hl':true, 'hlhover':isFormulaHighlighted('$id')}" id="$id"
        |  ng-mouseover="$$event.stopPropagation();highlightFormula('$id')"
        |  ng-mouseleave="$$event.stopPropagation();highlightFormula(undefined)"
        |  k4-droppable on-drop="dndSink('$id').formulaDrop(dragData)"
        |  on-drag-enter="dndSink('$id').formulaDragEnter(dragData)"
        |  on-drag-leave="dndSink('$id').formulaDragLeave(dragData)"
        |  ng-click="formulaClick('$id', $$event)"
        |  ng-right-click="formulaRightClick('$id', $$event)"
        |  uib-tooltip-template="'templates/formulaDndTooltipTemplate.html'"
        |  tooltip-placement="bottom"
        |  tooltip-trigger="none" tooltip-is-open="dndTooltip.isOpen('$id')"
        |  uib-popover-template="'templates/axiomPopoverTemplate.html'"
        |  popover-is-open="tacticPopover.isOpen('$id')"
        |  popover-trigger="none"
        |  popover-append-to-body="true"
        |  popover-placement="auto bottom"$HTML_CLOSE$content$HTML_OPEN/span$HTML_CLOSE""".stripMargin

  //@todo
  override def apply(seq: Sequent): String = ???

  // symmetric space depending on left/right/both having parentheses
  protected override def spaceLeft(t: BinaryComposite, leftPrint: String): String = (skipParensLeft(t), skipParensRight(t)) match {
    case (true, true) => leftPrint + (" " * balanceWeight(t))
    case (true, false) => leftPrint + (" " * weight(t.right, t))
    case (false, true) => leftPrint + (" " * weight(t.left, t))
    case (false, false) => leftPrint + " "
  }
  protected override def spaceRight(t: BinaryComposite, rightPrint: String): String = (skipParensLeft(t), skipParensRight(t)) match {
      case (true, true) => (" " * balanceWeight(t)) + rightPrint
      case (true, false) => (" " * weight(t.right, t)) + rightPrint
      case (false, true) => (" " * weight(t.left, t)) + rightPrint
      case (false, false) => " " + rightPrint
    }

  private def balanceWeight(par: BinaryComposite): Int = Math.max(weight(par.left, par), weight(par.right, par))

  protected override def weight(sub: Expression, par: BinaryComposite): Int = {
    val prec = op(par).prec
    val subPrec = op(sub).prec

    def prec2weight(prec: Int) =
      if (prec >= 200)
        // programs are formatted relative to one another not with their ridiculously large prec
        (prec-150) / 50
      else
        prec / 50

    // adapt own weight by sub operator weight
    (prec2weight(subPrec)/2) * prec2weight(prec)
  }

//  override val parser = new Parser() {
//    def apply(input: String): Expression = throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val termParser: (String => Term) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val formulaParser: (String => Formula) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val programParser: (String => Program) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val differentialProgramParser: (String => DifferentialProgram) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val printer: PrettyPrinter = UIKeYmaeraXPrettyPrinter.this
//  }
  override val fullPrinter: (Expression => String) = (e:Expression) => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.fullPrinter not implemented yet")
}
