/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.RenUSubst
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

/**
 * Sequential interpreter for Bellerophon tactic expressions.
  *
  * @param listeners Pre- and pos-processing hooks for step-wise tactic execution.
 * @author Nathan Fulton
 * @author Andre Platzer
 */
case class SequentialInterpreter(listeners : Seq[IOListener] = Seq()) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    if (Thread.currentThread().isInterrupted) {
      //@note end executing the interpreter when its thread gets interrupted
      //@todo throw an error that is easier to identify (for now: irrelevant, since Hydra Future already gone when we throw here)
      throw new BelleThrowable("Execution Stopped by interrupting the interpreter thread")
    }
    listeners.foreach(_.begin(v, expr))
    try {
      val result: BelleValue =
      expr match {
        case named: NamedTactic => apply(named.tactic, v)
        case builtIn: BuiltInTactic => v match {
          case BelleProvable(pr, _) => try {
            BelleProvable(builtIn.execute(pr))
          } catch {
            case e: BelleThrowable => throw e.inContext(BelleDot, pr.prettyString)
          }
          case _ => throw new BelleThrowable(s"Attempted to apply a built-in tactic to a value that is not a Provable: ${v.getClass.getName}").inContext(BelleDot, "")
        }
        case LabelBranch(label) => v match {
          case BelleProvable(pr, Some(labels)) => BelleProvable(pr, Some(labels :+ label))
          case BelleProvable(pr, None) => BelleProvable(pr, Some(label :: Nil))
          case _ => throw new BelleThrowable(s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}").inContext(BelleDot, "")
        }
        case (_: BuiltInPositionTactic) | (_:BuiltInLeftTactic) | (_:BuiltInRightTactic) | (_:BuiltInTwoPositionTactic) | (_:DependentPositionTactic) =>
          throw new BelleThrowable(s"Need to apply position tactic at a position before executing it: ${expr}(???)").inContext(expr, "")
        case AppliedPositionTactic(positionTactic, pos) => v match {
          case BelleProvable(pr, _) => try {
            BelleProvable(positionTactic.apply(pos).computeResult(pr))
          } catch {
            case e: BelleThrowable => throw e.inContext(positionTactic + " at " + pos, pr.prettyString)
          }
        }
        case positionTactic@AppliedBuiltinTwoPositionTactic(_, posOne, posTwo) => v match {
          case BelleProvable(pr, _) => try {
            BelleProvable(positionTactic.computeResult(pr))
          } catch {
            case e: BelleThrowable => throw e.inContext(positionTactic + " at " + posOne + ", " + posTwo, pr.prettyString)
          }
        }
        case SeqTactic(left, right) => {
          val leftResult = try {
            apply(left, v)
          } catch {
            case e: BelleThrowable => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
          }

          try {
            apply(right, leftResult)
          } catch {
            case e: BelleThrowable => throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
          }
        }
        case d: DependentTactic => try {
          val valueDependentTactic = d.computeExpr(v)
          apply(valueDependentTactic, v)
        } catch {
          case e: BelleThrowable => throw e.inContext(d, v.prettyString)
            //@todo unable to create is a serious error in the tactic not just an "oops whatever try something else exception"
          case e: Throwable => throw new BelleThrowable("Unable to create dependent tactic", e).inContext(d, "")
        }
        case it: InputTactic => try {
          apply(it.computeExpr(), v)
        } catch {
          case e: BelleThrowable => throw e.inContext(it, v.prettyString)
          case e: Throwable => throw new BelleThrowable("Unable to create input tactic", e).inContext(it, "")
        }
        case PartialTactic(child, _) => try {
          apply(child, v)
        } catch {
          case e: BelleThrowable => throw e.inContext(PartialTactic(e.context), "Tactic declared as partial failed to run: " + child)
        }
        case EitherTactic(left, right) => try {
          val leftResult = apply(left, v)
          (leftResult, left) match {
            case (BelleProvable(p, _), _) /*if p.isProved*/ => leftResult
            case (_, x: PartialTactic) => leftResult
            case _ => throw new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(BelleDot, right), "Failed left-hand side of |:" + left)
          }
        } catch {
          //@todo catch a little less. Just catching proper tactic exceptions, maybe some ProverExceptions et al., not swallow everything
          case eleft: BelleThrowable =>
            val rightResult = try {
              apply(right, v)
            } catch {
              case e: BelleThrowable => throw e.inContext(EitherTactic(eleft.context, e.context), "Failed: both left-hand side and right-hand side " + expr)
            }
            (rightResult, right) match {
              case (BelleProvable(p, _), _) /*if p.isProved*/ => rightResult
              case (_, x: PartialTactic) => rightResult
              case _ => throw new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(left, BelleDot), "Failed right-hand side of |: " + right)
            }
        }
        case SaturateTactic(child) =>
          var prev: BelleValue = null
          var result: BelleValue = v
          do {
            prev = result
            //@todo effect on listeners etc.
            try {
              result = apply(child, result)
            } catch {
              case e: BelleThrowable => /*@note child no longer applicable */ result = prev
            }
          } while (result != prev)
          result
        case RepeatTactic(child, times) =>
          var result = v
          for (i <- 1 to times) try {
            result = apply(child, result)
          } catch {
            case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
              "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
          }
          result
        case BranchTactic(children) => v match {
          case BelleProvable(p, _) =>
            if (children.length != p.subgoals.length)
              throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(expr, "")
            //Compute the results of piecewise applications of children to provable subgoals.
            val results: Seq[BelleProvable] =
              (children zip p.subgoals) map (pair => {
                val e_i = pair._1
                val s_i = pair._2
                val ithResult = try {
                  apply(e_i, bval(s_i))
                } catch {
                  case e: BelleThrowable => throw e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context)), "Failed on branch " + e_i)
                }
                ithResult match {
                  case b@BelleProvable(_, _) => b
                  case _ => throw new BelleThrowable("Each piecewise application in a Branching tactic should result in a provable.").inContext(expr, "")
                }
              })

            // Compute a single provable that contains the combined effect of all the piecewise computations.
            // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
            // is replaced with 0 new subgoals (also means: drop labels).
            def createLabels(start: Int, end: Int): List[BelleLabel] = (start until end).map(i => BelleTopLevelLabel(s"$i")).toList

            //@todo preserve labels from parent p (turn new labels into sublabels)
            val combinedEffect =
              results.foldLeft[(ProvableSig, Int, Option[List[BelleLabel]])]((p, 0, None))({ case ((cp: ProvableSig, cidx: Int, clabels: Option[List[BelleLabel]]), subderivation: BelleProvable) => {
                val (combinedProvable, nextIdx) = replaceConclusion(cp, cidx, subderivation.p)
                val combinedLabels: Option[List[BelleLabel]] = (clabels, subderivation.label) match {
                  case (Some(origLabels), Some(newLabels)) =>
                    Some(origLabels.patch(cidx, newLabels, 0))
                  case (Some(origLabels), None) =>
                    Some(origLabels.patch(cidx, createLabels(origLabels.length, origLabels.length + (nextIdx - cidx)), 0))
                  case (None, Some(newLabels)) =>
                    Some(createLabels(0, cidx) ++ newLabels)
                  case (None, None) => None
                }
                (combinedProvable, nextIdx, combinedLabels)
              }})
            BelleProvable(combinedEffect._1, if (combinedEffect._3.isEmpty) None else combinedEffect._3)
          case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(expr, "")
        }
        case OnAll(e) =>
          val provable = v match {
            case BelleProvable(p, _) => p
            case _ => throw new BelleThrowable("Cannot attempt OnAll with a non-Provable value.").inContext(expr, "")
          }
          //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
          try {
            apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), v)
          } catch {
            case e: BelleThrowable => throw e.inContext(OnAll(e.context), "")
          }

        case ChooseSome(options, e) =>
          val ec = e.asInstanceOf[Formula=>BelleExpr]
          //@todo specialization to A=Formula should be undone
          val opts: Iterator[Formula] = try {
            options().asInstanceOf[Iterator[Formula]]
          } catch {
            case err: IllegalArgumentException =>
              if (BelleExpr.DEBUG) println("ChooseSome: error listing options " + err)
              List[Formula]().iterator
          }
          var errors = ""
          while (opts.hasNext) {
            val o = opts.next()
            if (BelleExpr.DEBUG) println("ChooseSome: try " + o)
            val someResult: Option[BelleValue] = try {
              Some(apply(ec(o), v))
            } catch { case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None }
            if (BelleExpr.DEBUG) println("ChooseSome: try " + o + " got " + someResult)
            (someResult, e) match {
              case (Some(BelleProvable(p, _)), _) /*if p.isProved*/ => return someResult.get
              case (Some(_), x: PartialTactic) => return someResult.get
              case (Some(_), _) => errors += "option " + o + " " + new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
              case (None, _) => // option o had an error, so consider next option
            }
          }
          throw new BelleThrowable("ChooseSome did not succeed with any of its options").inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + opts.toList + "\n" + errors)

        case ProveAs(lemmaName, f, e) => {
          val BelleProvable(provable, labels) = v
          assert(provable.subgoals.length == 1)

          val lemma = ProvableSig.startProof(f)

          //Prove the lemma iff it's not already proven.
          if(LemmaDBFactory.lemmaDB.contains(lemmaName)) {
            assert(LemmaDBFactory.lemmaDB.get(lemmaName).head.fact.conclusion == lemma.conclusion)
          }
          else {
            val BelleProvable(result, resultLabels) = apply(e, BelleProvable(lemma))
            assert(result.isProved, "Result of proveAs should always be proven.")

            val tacticText: String = try { BellePrettyPrinter(e) } catch { case _ => "nil" }

            val evidence = ToolEvidence(List(
              "tool" -> "KeYmaera X",
              "model" -> lemma.prettyString,
              "tactic" -> tacticText,
              "proof" -> "" //@todo serialize proof
            )) :: Nil

            //Save the lemma.
            LemmaDBFactory.lemmaDB.add(Lemma(result, Lemma.requiredEvidence(result, evidence), Some(lemmaName)))
          }
          v //nop on the original goal.
        }

        case Let(abbr, value, inner) =>
          val (provable,lbl) = v match {
            case BelleProvable(p, l) => (p,l)
            case _ => throw new BelleThrowable("Cannot attempt Let with a non-Provable value.").inContext(expr, "")
          }
          if (provable.subgoals.length != 1)
            throw new BelleThrowable("Let of multiple goals is not currently supported.").inContext(expr, "")

          import Augmentors.SequentAugmentor
          //@todo sometimes may want to offer some unification for: let j(x)=x^2>0 in tactic for sequent mentioning both x^2>0 and (x+y)^2>0 so j(x) and j(x+y).
          val us: USubst = USubst(SubstitutionPair(abbr, value) :: Nil)
          val in: ProvableSig = ProvableSig.startProof(provable.subgoals.head.replaceAll(value, abbr))
          println("INFO: " + expr + " considers\n" + in + "\nfor outer\n" + provable)
          //assert(us(in.conclusion) == provable.subgoals.head, "backsubstitution will ultimately succeed from\n" + in + "\nvia " + us + " to outer\n" + provable)
          apply(inner, new BelleProvable(in)) match {
            case BelleProvable(derivation, _) =>
              val backsubst: ProvableSig = derivation(us)
              BelleProvable(provable(backsubst,0), lbl)
            case e => throw new BelleThrowable("Let expected sub-derivation")
          }

        case LetInspect(abbr, instantiator, inner) =>
          val (provable,lbl) = v match {
            case BelleProvable(p, l) => (p,l)
            case _ => throw new BelleThrowable("Cannot attempt LetInspect with a non-Provable value.").inContext(expr, "")
          }
          if (provable.subgoals.length != 1)
            throw new BelleThrowable("LetInspect of multiple goals is not currently supported.").inContext(expr, "")

          val in: ProvableSig = ProvableSig.startProof(provable.subgoals.head)
          apply(inner, new BelleProvable(in)) match {
            case BelleProvable(derivation, _) =>
              try {
                val value: Expression = instantiator(derivation)
                val us: USubst = USubst(SubstitutionPair(abbr, value) :: Nil)
                val backsubst: ProvableSig = derivation(us)
                BelleProvable(provable(backsubst, 0), lbl)
              } catch {
                case e: BelleThrowable => throw e.inContext(expr, "LetInspect backsubstitution failed")
                case e: ProverException => throw new BelleThrowable("LetInspect backsubstitution failed", e).inContext(expr.toString, "LetInspect backsubstitution failed")
              }
            case e => throw new BelleThrowable("LetInspect expected sub-derivation")
          }

        case t@USubstPatternTactic(children) => {
          val provable = v match {
            case BelleProvable(p, _) => p
            case _ => throw new BelleThrowable("Cannot attempt US unification with a non-Provable value.").inContext(expr, "")
          }

          if (provable.subgoals.length != 1)
            throw new BelleThrowable("Unification of multi-sequent patterns is not currently supported.").inContext(expr, "")

          //@todo loop through all using the first one whose unificatoin and tactic application ends up being successful as opposed to committing to first unifiable case.
          //Attempt to find a child that unifies with the input.
          val unifications = children.map(pair => {
            val ty = pair._1
            val expr = pair._2
            ty match {
              case SequentType(s) => try {
                (UnificationMatch(s, provable.subgoals.head), expr)
              } catch {
                // in contrast to .unifiable, this suppresses "Sequent un-unifiable Un-Unifiable" message, which clutter STDIO.
                // fall back to user-provided substitution
                case e: UnificationException =>
                  //if (DEBUG) println("USubst Pattern Incomplete -- could not find a unifier for any option" + t)
                  (RenUSubst(Nil), expr)
              }
              case _ => throw new BelleThrowable("Cannot unify non-sequent types.").inContext(t, "")
            }
          })

          //@note try user-provided last unification
          val unification: (UnificationMatch.Subst, RenUSubst => BelleExpr) =
            if (unifications.forall(_._1.isEmpty)) unifications.last
            else unifications.filterNot(_._1.isEmpty).head

          apply(unification._2(unification._1.asInstanceOf[RenUSubst]), v)
        }

        case AppliedDependentTwoPositionTactic(t, p1, p2) => {
          val provable = v match {
            case BelleProvable(p,_) => p
            case _ => throw new BelleThrowable("two position tactics can only be run on Provables.")
          }
          apply(t.computeExpr(p1, p2).computeExpr(provable), v)
        }
      }
      listeners.foreach(l => l.end(v, expr, Left(result)))
      result
    } catch {
      case err:BelleThrowable =>
        listeners.foreach(l => l.end(v, expr, Right(err)))
        throw err
      case e:Throwable => println(s"Unknown exception running $expr: $e\nDatabase recording is incomplete!"); throw e
    }
  }

  /** Maps sequents to BelleProvables. */
  private def bval(s: Sequent) = BelleProvable(ProvableSig.startProof(s))

  /**
   * Replaces the nth subgoal of original with the remaining subgoals of result.
    *
    * @param original A Provable whose nth subgoal is equal to "result".
   * @param n The numerical index of the subgoal of original to rewrite (Seqs are zero-indexed)
   * @param subderivation
   * @return A pair of:
   *         * A new provable that is identical to original, except that the nth subgoal is replaced with the remaining subgoals of result; and
   *         * The new index of the (n+1)th goal. //@todo clarify
   * @todo result is undefined. Subderivation rather
   */
  private def replaceConclusion(original: ProvableSig, n: Int, subderivation: ProvableSig): (ProvableSig, Int) = {
    assert(original.subgoals.length > n, s"$n is a bad index for Provable with ${original.subgoals.length} subgoals: $original")
    if(original.subgoals(n) != subderivation.conclusion)
      throw new BelleThrowable(s"Subgoal #$n of the original provable (${original.subgoals(n)}}) should be equal to the conclusion of the subderivation (${subderivation.conclusion}})")
    val newProvable = original(subderivation, n)
    val nextIdx = if(subderivation.isProved) n else n + 1
    (newProvable, nextIdx)
  }
}