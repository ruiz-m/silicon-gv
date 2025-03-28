// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

<<<<<<< HEAD
import viper.silver.ast
import viper.silver.ast.Exp
import viper.silver.ast.Node

import java.util.concurrent._
import viper.silicon.common.concurrency._
import viper.silicon.interfaces.{Unreachable, VerificationResult, Success, Failure}
import viper.silicon.logger.SymbExLogger
import viper.silicon.state.{State, CheckPosition, runtimeChecks, BranchCond}
import viper.silicon.state.terms.{Not, Term}
import viper.silicon.supporters.Translator
import viper.silicon.utils
import viper.silicon.verifier.Verifier
=======
import java.util.concurrent._
import viper.silicon.common.concurrency._
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.reporting.condenseToViperResult
import viper.silicon.state.State
import viper.silicon.state.terms.{FunctionDecl, MacroDecl, Not, Term}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.reporter.BranchFailureMessage
import viper.silver.verifier.Failure

import scala.collection.immutable.HashSet
>>>>>>> upstream/master

trait BranchingRules extends SymbolicExecutionRules {
  def branch(s: State,
             condition: Term,
<<<<<<< HEAD
             position: ast.Exp,
             origin: Option[CheckPosition],
=======
             conditionExp: (ast.Exp, Option[ast.Exp]),
>>>>>>> upstream/master
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fTrue: (State, Verifier) => VerificationResult,
             fFalse: (State, Verifier) => VerificationResult)
            : VerificationResult
}

<<<<<<< HEAD
object brancher extends BranchingRules with Immutable {
  def branch(s: State,
             condition: Term,
             position: ast.Exp,
             origin: Option[CheckPosition],
=======
object brancher extends BranchingRules {
  def branch(s: State,
             condition: Term,
             conditionExp: (ast.Exp, Option[ast.Exp]),
>>>>>>> upstream/master
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fThen: (State, Verifier) => VerificationResult,
             fElse: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val negatedCondition = Not(condition)
<<<<<<< HEAD
    val parallelizeElseBranch = s.parallelizeBranches && !s.underJoin
    val (g, h, oh) = s.oldStore match {
      case Some(store) => (store, s.h + s.oldHeaps(Verifier.PRE_HEAP_LABEL), s.optimisticHeap + s.oldHeaps(Verifier.PRE_OPTHEAP_LABEL))
      case None => (s.g, s.h, s.optimisticHeap)
    }
=======
    val negatedConditionExp = ast.Not(conditionExp._1)(pos = conditionExp._1.pos, info = conditionExp._1.info, ast.NoTrafos)
    val negatedConditionExpNew = conditionExp._2.map(ce => ast.Not(ce)(pos = ce.pos, info = ce.info, ast.NoTrafos))

>>>>>>> upstream/master

    /* Skip path feasibility check if one of the following holds:
     *   (1) the branching is due to the short-circuiting evaluation of a conjunction
     *   (2) the branch condition contains a quantified variable
     */
    val skipPathFeasibilityCheck = (
         fromShortCircuitingAnd
      || (   s.quantifiedVariables.nonEmpty
<<<<<<< HEAD
          && s.quantifiedVariables.exists(condition.freeVariables.contains))
=======
          && s.quantifiedVariables.map(_._1).exists(condition.freeVariables.contains))
>>>>>>> upstream/master
    )

    /* True if the then-branch is to be explored */
    val executeThenBranch = (
         skipPathFeasibilityCheck
      || !v.decider.check(negatedCondition, Verifier.config.checkTimeout()))

    /* False if the then-branch is to be explored */
    val executeElseBranch = (
         !executeThenBranch /* Assumes that ast least one branch is feasible */
      || skipPathFeasibilityCheck
      || !v.decider.check(condition, Verifier.config.checkTimeout()))

<<<<<<< HEAD
=======
    val parallelizeElseBranch = s.parallelizeBranches && executeThenBranch && executeElseBranch

>>>>>>> upstream/master
//    val additionalPaths =
//      if (executeThenBranch && exploreFalseBranch) 1
//      else 0

//    bookkeeper.branches += additionalPaths

    val cnt = v.counter(this).next()

    val thenBranchComment = s"[then-branch: $cnt | $condition | ${if (executeThenBranch) "live" else "dead"}]"
    val elseBranchComment = s"[else-branch: $cnt | $negatedCondition | ${if (executeElseBranch) "live" else "dead"}]"

    v.decider.prover.comment(thenBranchComment)
    v.decider.prover.comment(elseBranchComment)

<<<<<<< HEAD
    val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(2, Some(condition))

    val elseBranchVerificationTask: Verifier => VerificationResult =
      if (executeElseBranch) {
/* [BRANCH-PARALLELISATION] */
=======
    var elseBranchVerifier: String = null

    val uidBranchPoint = v.symbExLog.insertBranchPoint(2, Some(condition), Some(conditionExp._1))
    var functionsOfCurrentDecider: Set[FunctionDecl] = null
    var macrosOfCurrentDecider: Vector[MacroDecl] = null
    var proverArgsOfCurrentDecider: viper.silicon.Map[String, String] = null
    var wasElseExecutedOnDifferentVerifier = false
    var functionsOfElseBranchDecider: Set[FunctionDecl] = null
    var proverArgsOfElseBranchDecider: viper.silicon.Map[String, String] = null
    var macrosOfElseBranchDecider: Seq[MacroDecl] = null
    var pcsForElseBranch: PathConditionStack = null
    var noOfErrors = 0

    val elseBranchVerificationTask: Verifier => VerificationResult =
      if (executeElseBranch) {
        /* [BRANCH-PARALLELISATION] */
>>>>>>> upstream/master
        /* Compute the following sets
         *   1. only if the else-branch needs to be explored
         *   2. right now, i.e. not when the exploration actually takes place
         * The first requirement avoids computing the sets in cases where they are not
         * needed, the second one ensures that the current path conditions (etc.) of the
         * "offloading" verifier are captured.
         */
<<<<<<< HEAD
//        val functionsOfCurrentDecider = v.decider.freshFunctions
//        val macrosOfCurrentDecider = v.decider.freshMacros
//        val pcsOfCurrentDecider = v.decider.pcs.duplicate()

//        println(s"\n[INIT elseBranchVerificationTask v.uniqueId = ${v.uniqueId}]")
//        println(s"  condition = $condition")
//        println("  v.decider.pcs.assumptions = ")
//        v.decider.pcs.assumptions foreach (a => println(s"    $a"))
//        println("  v.decider.pcs.branchConditions = ")
//        v.decider.pcs.branchConditions foreach (a => println(s"    $a"))

        (v0: Verifier) => {
          SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
          SymbExLogger.currentLog().markReachable(uidBranchPoint)
          executionFlowController.locally(s, v0)((s1, v1) => {
            if (v.uniqueId != v1.uniqueId) {

              /* [BRANCH-PARALLELISATION] */
              throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")

//                val newFunctions = functionsOfCurrentDecider -- v1.decider.freshFunctions
//                val newMacros = macrosOfCurrentDecider.diff(v1.decider.freshMacros)
//
//                v1.decider.prover.comment(s"[Shifting execution from ${v.uniqueId} to ${v1.uniqueId}]")
//                v1.decider.prover.comment(s"Bulk-declaring functions")
//                v1.decider.declareAndRecordAsFreshFunctions(newFunctions)
//                v1.decider.prover.comment(s"Bulk-declaring macros")
//                v1.decider.declareAndRecordAsFreshMacros(newMacros)
//
//                v1.decider.prover.comment(s"Taking path conditions from source verifier ${v.uniqueId}")
//                v1.decider.setPcs(pcsOfCurrentDecider)
//                v1.decider.pcs.pushScope() /* Empty scope for which the branch condition can be set */
            }

            v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
            val negCond: Exp =
              (new Translator(s1.copy(g = g, h = h, optimisticHeap = oh), v1.decider.pcs).translate(negatedCondition) match {
                case None => sys.error("Error translating! Exiting safely.")
                case Some(expr) => expr
              })
            v1.decider.setCurrentBranchCondition(negatedCondition, negCond, position, origin)

            fElse(stateConsolidator.consolidateIfRetrying(s1, v1), v1)
=======
        if (parallelizeElseBranch){
          functionsOfCurrentDecider = v.decider.freshFunctions
          macrosOfCurrentDecider = v.decider.freshMacros
          proverArgsOfCurrentDecider = v.decider.getProverOptions()
          pcsForElseBranch = v.decider.pcs.duplicate()
          noOfErrors = v.errorsReportedSoFar.get()
        }

        (v0: Verifier) => {
          v0.symbExLog.switchToNextBranch(uidBranchPoint)
          v0.symbExLog.markReachable(uidBranchPoint)
          if (v.uniqueId != v0.uniqueId){
            /* [BRANCH-PARALLELISATION] */
            // executing the else branch on a different verifier, need to adapt the state
            wasElseExecutedOnDifferentVerifier = true

            val newFunctions = functionsOfCurrentDecider -- v0.decider.freshFunctions
            val v0FreshMacros = HashSet.from(v0.decider.freshMacros)
            val newMacros = macrosOfCurrentDecider.filter(m => !v0FreshMacros.contains(m))

            v0.decider.prover.comment(s"[Shifting execution from ${v.uniqueId} to ${v0.uniqueId}]")
            proverArgsOfElseBranchDecider = v0.decider.getProverOptions()
            v0.decider.resetProverOptions()
            v0.decider.setProverOptions(proverArgsOfCurrentDecider)
            v0.decider.prover.comment(s"Bulk-declaring functions")
            v0.decider.declareAndRecordAsFreshFunctions(newFunctions)
            v0.decider.prover.comment(s"Bulk-declaring macros")
            v0.decider.declareAndRecordAsFreshMacros(newMacros)

            v0.decider.prover.comment(s"Taking path conditions from source verifier ${v.uniqueId}")
            v0.decider.setPcs(pcsForElseBranch)
            v0.errorsReportedSoFar.set(noOfErrors)
          }
          elseBranchVerifier = v0.uniqueId

          executionFlowController.locally(s, v0)((s1, v1) => {
            v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
            v1.decider.setCurrentBranchCondition(negatedCondition, (negatedConditionExp, negatedConditionExpNew))

            var functionsOfElseBranchdDeciderBefore: Set[FunctionDecl] = null
            var nMacrosOfElseBranchDeciderBefore: Int = 0

            if (v.uniqueId != v0.uniqueId) {
              v1.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
              if (s.underJoin) {
                nMacrosOfElseBranchDeciderBefore = v1.decider.freshMacros.size
                functionsOfElseBranchdDeciderBefore = v1.decider.freshFunctions
              }
            }

            val result = fElse(v1.stateConsolidator(s1).consolidateOptionally(s1, v1), v1)
            if (wasElseExecutedOnDifferentVerifier) {
              v1.decider.resetProverOptions()
              v1.decider.setProverOptions(proverArgsOfElseBranchDecider)
              if (s.underJoin) {
                functionsOfElseBranchDecider = v1.decider.freshFunctions -- functionsOfElseBranchdDeciderBefore
                macrosOfElseBranchDecider = v1.decider.freshMacros.drop(nMacrosOfElseBranchDeciderBefore)
              }
            }
            result
>>>>>>> upstream/master
          })
        }
      } else {
        _ => Unreachable()
      }

    val elseBranchFuture: Future[Seq[VerificationResult]] =
      if (executeElseBranch) {
        if (parallelizeElseBranch) {
          /* [BRANCH-PARALLELISATION] */
<<<<<<< HEAD
          throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")
//          v.verificationPoolManager.queueVerificationTask(v0 => {
//            v0.verificationPoolManager.runningVerificationTasks.put(elseBranchVerificationTask, true)
//            val res = elseBranchVerificationTask(v0)
//
//            v0.verificationPoolManager.runningVerificationTasks.remove(elseBranchVerificationTask)
//
//            Seq(res)
//          })
=======
          v.verificationPoolManager.queueVerificationTask(v0 => {
            val res = elseBranchVerificationTask(v0)

            Seq(res)
          })
>>>>>>> upstream/master
        } else {
          new SynchronousFuture(Seq(elseBranchVerificationTask(v)))
        }
      } else {
        CompletableFuture.completedFuture(Seq(Unreachable()))
      }

<<<<<<< HEAD
    val rsThen: VerificationResult = (if (executeThenBranch) {
      SymbExLogger.currentLog().markReachable(uidBranchPoint)
      executionFlowController.locally(s, v)((s1, v1) => {
        v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
        val cond: Exp =
          (new Translator(s1.copy(g = g, h = h, optimisticHeap = oh), v1.decider.pcs).translate(condition) match {
            case None => sys.error("Error translating! Exiting safely.")
            case Some(expr) => expr
          })
        v1.decider.setCurrentBranchCondition(condition, cond, position, origin)

        fThen(stateConsolidator.consolidateIfRetrying(s1, v1), v1)
      })
    } else {
      Unreachable()
    })

    val rsElse: VerificationResult = {

      /* [BRANCH-PARALLELISATION] */
      if (parallelizeElseBranch) {
//          && v.verificationPoolManager.slaveVerifierPool.getNumIdle == 0
//          && !v.verificationPoolManager.runningVerificationTasks.containsKey(elseBranchVerificationTask)
//                /* TODO: This attempt to ensure that the elseBranchVerificationTask is not already
//                 *       being executed is most likely not thread-safe since checking if a task
//                 *       is still in the queue and canceling it, if so, is not an atomic operation.
//                 *       I.e. the task may be taken out of the queue in between.
//                 */

        throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")

//        /* Cancelling the task should result in the underlying task being removed from the task
//         * queue/executor
//         */
//        elseBranchFuture.cancel(true)
//
//        /* Run the task on the current thread */
//        elseBranchVerificationTask(v)
      } else {
        var rs: Seq[VerificationResult] = null
        try {
          rs = elseBranchFuture.get()
        } catch {
          case ex: ExecutionException =>
            ex.getCause.printStackTrace()
            throw ex
        }

        assert(rs.length == 1, s"Expected a single verification result but found ${rs.length}")
        rs.head
      }
    }

    SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
    if (s.isImprecise && !fromShortCircuitingAnd) {
      rsThen match {
        case Success() => {
          rsElse match {
            case Success() | Unreachable() => Success()
            case Failure(m1) => {
              /* run-time check for rsThen branch */
              val cond: Exp =
                (new Translator(s.copy(g = g, h = h, optimisticHeap = oh), v.decider.pcs).translate(condition) match {
                  case None => sys.error("Error translating! Exiting safely.")
                  case Some(expr) => expr
                })

              // It's okay to not look in the state for the right position here,
              // because we already look in the state to pass the correct position
              // into branch
              val runtimeCheckAstNode: CheckPosition =
                origin match {
                  case Some(checkPosNode) => checkPosNode
                  case None => CheckPosition.GenericNode(position)
                }

              if (s.generateChecks) {
                runtimeChecks.addChecks(runtimeCheckAstNode,
                  cond,
                  viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                    v.decider.pcs.branchConditionsAstNodes,
                    v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                  position.asInstanceOf[Exp],
                  false)
              }

              Success()
              /* TODO: eventually should warn about failing branch to users - JW */
            }
          }
        }
        case Unreachable() => {
          rsElse match {
            case Success() | Failure(_) => rsElse
            case Unreachable() => Unreachable()
          }
        }
        case Failure(m1) => {
          rsElse match {
            case Success() => {
              /* run-time check for rsElse branch */
              val negCond: Exp =
                (new Translator(s.copy(g = g, h = h, optimisticHeap = oh), v.decider.pcs).translate(negatedCondition) match {
                  case None => sys.error("Error translating! Exiting safely.")
                  case Some(expr) => expr
                })

              val runtimeCheckAstNode: CheckPosition =
                origin match {
                  case Some(checkPosNode) => checkPosNode
                  case None => CheckPosition.GenericNode(position)
                }

              if (s.generateChecks) {
                runtimeChecks.addChecks(runtimeCheckAstNode,
                  negCond,
                  viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                    v.decider.pcs.branchConditionsAstNodes,
                    v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                  position.asInstanceOf[Exp],
                  false)
              }

              Success()
              /* TODO: eventually should warn about failing branch to users - JW */
            }
            case Unreachable() => rsThen
            case Failure(m2) => rsThen && rsElse
          }
        }
      }
    } else {
      (rsThen && rsElse)
    }
=======
    val res = {
      val thenRes = if (executeThenBranch) {
          v.symbExLog.markReachable(uidBranchPoint)
          executionFlowController.locally(s, v)((s1, v1) => {
            v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
            v1.decider.setCurrentBranchCondition(condition, conditionExp)

            fThen(v1.stateConsolidator(s1).consolidateOptionally(s1, v1), v1)
          })
        } else {
          Unreachable()
        }
      if (thenRes.isFatal && !thenRes.isReported && s.parallelizeBranches && s.isLastRetry) {
        thenRes.isReported = true
        v.reporter.report(BranchFailureMessage("silicon", s.currentMember.get.asInstanceOf[ast.Member with Serializable],
          condenseToViperResult(Seq(thenRes)).asInstanceOf[Failure]))
      }
      thenRes
    }.combine({

      /* [BRANCH-PARALLELISATION] */
      var rs: Seq[VerificationResult] = null
      try {
        if (parallelizeElseBranch) {
          val pcsAfterThenBranch = v.decider.pcs.duplicate()
          val noOfErrorsAfterThenBranch = v.errorsReportedSoFar.get()

          val pcsBefore = v.decider.pcs

          rs = elseBranchFuture.get()

          if (v.decider.pcs != pcsBefore && v.uniqueId != elseBranchVerifier){
            // we have done other work during the join, need to reset
            v.decider.prover.comment(s"Resetting path conditions after interruption")
            v.decider.setPcs(pcsAfterThenBranch)
            v.errorsReportedSoFar.set(noOfErrorsAfterThenBranch)
            v.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
            v.decider.resetProverOptions()
            v.decider.setProverOptions(proverArgsOfCurrentDecider)
          }
        } else {
          rs = elseBranchFuture.get()
        }
      } catch {
        case ex: ExecutionException =>
          ex.getCause.printStackTrace()
          throw ex
      }

      assert(rs.length == 1, s"Expected a single verification result but found ${rs.length}")
      if (rs.head.isFatal && !rs.head.isReported && s.parallelizeBranches && s.isLastRetry) {
        rs.head.isReported = true
        v.reporter.report(BranchFailureMessage("silicon", s.currentMember.get.asInstanceOf[ast.Member with Serializable],
          condenseToViperResult(Seq(rs.head)).asInstanceOf[Failure]))
      }
      rs.head

    }, alwaysWaitForOther = parallelizeElseBranch)
    v.symbExLog.endBranchPoint(uidBranchPoint)
    if (wasElseExecutedOnDifferentVerifier && s.underJoin) {

      v.decider.prover.comment(s"[To continue after join, adding else branch functions and macros to current verifier.]")
      v.decider.prover.comment(s"Bulk-declaring functions")
      v.decider.declareAndRecordAsFreshFunctions(functionsOfElseBranchDecider)
      v.decider.prover.comment(s"Bulk-declaring macros")
      v.decider.declareAndRecordAsFreshMacros(macrosOfElseBranchDecider)
    }
    res
>>>>>>> upstream/master
  }
}
