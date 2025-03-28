// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.Config.JoinMode

import scala.annotation.unused
import viper.silver.cfg.silver.SilverCfg
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge}
import viper.silver.verifier.{CounterexampleTransformer, PartialVerificationError}
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._
import viper.silver.{ast, cfg}
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
<<<<<<< HEAD
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data._
import viper.silicon.resources.FieldID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.Translator
import viper.silicon.utils.{freshSnap, zip3}
import viper.silicon.utils.consistency.createUnexpectedNodeError
=======
import viper.silicon.logger.records.data.{CommentRecord, ConditionalEdgeRecord, ExecuteRecord, MethodCallRecord}
import viper.silicon.resources.FieldID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.utils.ast.{BigAnd, extractPTypeFromExp, simplifyVariableName}
import viper.silicon.utils.freshSnap
>>>>>>> upstream/master
import viper.silicon.verifier.Verifier
import viper.silver.cfg.{ConditionalEdge, StatementBlock}

trait ExecutionRules extends SymbolicExecutionRules {
  def exec(s: State,
           cfg: SilverCfg,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def exec(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def execs(s: State, stmts: Seq[ast.Stmt], v: Verifier)
           (Q: (State, Verifier) => VerificationResult)
           : VerificationResult
}

<<<<<<< HEAD
object executor extends ExecutionRules with Immutable {

=======
object executor extends ExecutionRules {
>>>>>>> upstream/master
  import consumer._
  import evaluator._
  import producer._
  import wellFormedness._

<<<<<<< HEAD
  private def follow(s: State, originatingBlock: SilverBlock, edge: SilverEdge, v: Verifier)
=======
  private def follow(s: State, edge: SilverEdge, v: Verifier, joinPoint: Option[SilverBlock])
>>>>>>> upstream/master
                    (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

<<<<<<< HEAD
    def handleOutEdge(s: State, originatingBlock: SilverBlock, edge: SilverEdge, v: Verifier) = {
      // state after loop is created here?
      edge.kind match {
        // in edges go into loops
        // out edges lead out of loops (and maybe to another loop)
        // normal edges are between statements (which are not loops)
        case cfg.Kind.Out => {
          val (fr1, h1) = stateConsolidator.merge(s.functionRecorder, s.h, s.invariantContexts.head._3, v)
          val (fr2, oh) = stateConsolidator.merge(fr1, s.optimisticHeap, s.invariantContexts.head._4, v)

          val potentialCheckPosition: Option[CheckPosition.Loop] = {
            val loopInvariant = originatingBlock match {
              case cfg.LoopHeadBlock(invs, _) => Some(invs)
              case _ => None
            }

            loopInvariant match {
              case Some(invs) => Some(CheckPosition.Loop(invs, LoopPosition.After))
              case None => None
            }
          }

          val s1 = s.copy(functionRecorder = fr2,
            isImprecise = s.invariantContexts.head._2, h = h1, optimisticHeap = oh,
            invariantContexts = s.invariantContexts.tail,
            loopPosition = potentialCheckPosition)

          s1
        }
        case _ =>
          /* No need to do anything special. See also the handling of loop heads in exec below. */
          s
=======

    joinPoint match {
      case Some(jp) if jp == edge.target =>
        // Join point reached, stop following edges.
        val s1 = handleOutEdge(s, edge, v)
        Q(s1, v)

      case _ => edge match {
        case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] =>
          val condEdgeRecord = new ConditionalEdgeRecord(ce.condition, s, v.decider.pcs)
          val sepIdentifier = v.symbExLog.openScope(condEdgeRecord)
          val s1 = handleOutEdge(s, edge, v)
          eval(s1, ce.condition, IfFailed(ce.condition), v)((s2, tCond, condNew, v1) =>
            /* Using branch(...) here ensures that the edge condition is recorded
             * as a branch condition on the pathcondition stack.
             */
            brancher.branch(s2.copy(parallelizeBranches = false), tCond, (ce.condition, condNew), v1)(
              (s3, v3) =>
                exec(s3.copy(parallelizeBranches = s2.parallelizeBranches), ce.target, ce.kind, v3, joinPoint)((s4, v4) => {
                  v4.symbExLog.closeScope(sepIdentifier)
                  Q(s4, v4)
                }),
              (_, v3) => {
                v3.symbExLog.closeScope(sepIdentifier)
                Success()
              }))

        case ue: cfg.UnconditionalEdge[ast.Stmt, ast.Exp] =>
          val s1 = handleOutEdge(s, edge, v)
          exec(s1, ue.target, ue.kind, v, joinPoint)(Q)
>>>>>>> upstream/master
      }
      // set the after loop state here
    }
  }

<<<<<<< HEAD
    // TODO: ASK JENNA where the loop location needs to be available here
    // we continue after the loop here
    // conditional edge: follow came from a loop
    edge match {
      case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] =>
        val condEdgeRecord = new ConditionalEdgeRecord(ce.condition, s, v.decider.pcs)
        val sepIdentifier = SymbExLogger.currentLog().openScope(condEdgeRecord)
        val s1 = handleOutEdge(s, originatingBlock, edge, v)
        // condition being negated here
        eval(s1, ce.condition, IfFailed(ce.condition), v)((s2, tCond, v1) => {
        /* Eval here likely results in the creation of two run-time checks for the same field when framing loop conditions:
         * one in this eval + one in the eval in the loop block IN-edge case, both located before the loop.
         * It will also create one for framing !e after loop, which is correct and should be kept. - JW
         */
          /* Using branch(...) here ensures that the edge condition is recorded
           * as a branch condition on the pathcondition stack.
           */

          val s2point5 = s2.copy(loopPosition = None)
          val positionalCondition = ce.condition match {
            case ast.Not(e) => e
            case _ => ce.condition
          }

          // The loop location should be set for this branch, maybe
          brancher.branch(s2point5, tCond, positionalCondition, s1.loopPosition, v1)(
            (s3, v3) =>
              exec(s3, ce.target, ce.kind, v3)((s4, v4) => {
                SymbExLogger.currentLog().closeScope(sepIdentifier)
                Q(s4, v4)
              }),
            (_, _) => {
              SymbExLogger.currentLog().closeScope(sepIdentifier)
              Unreachable()
            })
        })

      // TODO: Should we be tracking loop positions here, too?
      case ue: cfg.UnconditionalEdge[ast.Stmt, ast.Exp] =>

        val s1 = handleOutEdge(s, originatingBlock, edge, v)
        val s1point5 = s1.copy(loopPosition = None)

        exec(s1point5, ue.target, ue.kind, v)(Q)
=======
  def handleOutEdge(s: State, edge: SilverEdge, v: Verifier): State = {
    edge.kind match {
      case cfg.Kind.Out =>
        val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, s, s.h, s.invariantContexts.head, v)
        val s1 = s.copy(functionRecorder = fr1, h = h1,
          invariantContexts = s.invariantContexts.tail)
        s1
      case _ =>
        /* No need to do anything special. See also the handling of loop heads in exec below. */
        s
>>>>>>> upstream/master
    }
  }

  private def follows(s: State,
                      originatingBlock: SilverBlock,
                      edges: Seq[SilverEdge],
                      @unused pvef: ast.Exp => PartialVerificationError,
                      v: Verifier,
                      joinPoint: Option[SilverBlock])
                     (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

<<<<<<< HEAD
    if (edges.isEmpty) {
      Q(s, v)
    } else {
      val isImprecise = originatingBlock match {
        case cfg.LoopHeadBlock(_, _) => s.invariantContexts.head._1
        case _ => s.isImprecise
      }
      if (isImprecise) {
        val uidBranchPoint = if (edges.length > 1) { SymbExLogger.currentLog().insertBranchPoint(edges.length) } else { 0 }
        val rsTuple =
        edges.zipWithIndex.foldLeft((Unreachable(): VerificationResult, edges.head: SilverEdge)) { (rs, eTuple) =>
          val (edge, edgeIndex) = eTuple
          if (edges.length > 1) {
            if (edgeIndex != 0) {
              SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
            }
            SymbExLogger.currentLog().markReachable(uidBranchPoint)
          }
          val rsEdge = follow(s, originatingBlock, edge, v)(Q)
          rs match {
            case (Success(), prevEdge) => {
              rsEdge match {
                case Success() | Unreachable() => (Success(), edge)
                case Failure(m) => {
                  edge match {
                    case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => {
                      edge.kind match {
                        case cfg.Kind.Out => (Failure(m), edge)
                        case _ => {
                          /* run-time check */
                          val position: ast.Exp =
                            prevEdge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition match {
                              case ast.Not(e: ast.Exp) => e
                              case e: ast.Exp => e
                            }

                          if (s.generateChecks) {
                            runtimeChecks.addChecks(CheckPosition.GenericNode(position),
                              prevEdge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition,
                              viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                                v.decider.pcs.branchConditionsAstNodes,
                                v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                              position,
                              false)
                          }

                          (Success(), edge)
                        }
                      }
                    }
                    case _ => (Failure(m), edge)
                  }
                }
              }
            }
            case (Unreachable(), prevEdge) => (rsEdge, edge)
            case (Failure(m), prevEdge) => {
              rsEdge match {
                case Success() => {
                  edge match {
                    case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => {
                      prevEdge.kind match {
                        case cfg.Kind.Out => (Failure(m), edge)
                        case _ => {
                          /* run-time check */
                          val position: ast.Exp =
                            edge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition match {
                              case ast.Not(e: ast.Exp) => e
                              case e: ast.Exp => e
                            }
                          if (s.generateChecks) {
                            runtimeChecks.addChecks(CheckPosition.GenericNode(position),
                              edge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition,
                              viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                                v.decider.pcs.branchConditionsAstNodes,
                                v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                              position,
                              false)
                          }

                          (Success(), edge)
                        }
                      }
                    }
                    case _ => (Failure(m), edge)
                  }
                }
                case Unreachable() => (rs._1, edge)
                case Failure(_) => (rs._1 && rsEdge, edge)
              }
            }
          }
        }
        if (edges.length > 1) {
          SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
        }
        rsTuple._1
      } else {
        // if not imprecise
        if (edges.length == 1) {
          follow(s, originatingBlock, edges.head, v)(Q)
        } else {
          val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(edges.length)
          val res = edges.zipWithIndex.foldLeft(Success(): VerificationResult) {
            case (fatalResult: FatalResult, _) => fatalResult
            case (_, (edge, edgeIndex)) =>
              if (edgeIndex != 0) {
                SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
              }
              SymbExLogger.currentLog().markReachable(uidBranchPoint)
              follow(s, originatingBlock, edge, v)(Q)
          }
          SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
          res
        }
      }
=======
    // If joining branches is enabled, find join point if it exists.
    val jp: Option[SilverBlock] = if (s.moreJoins.id >= JoinMode.All.id) {
      edges.headOption.flatMap(edge => s.methodCfg.joinPoints.get(edge.source))
    } else {
      None
    }

    (edges, jp) match {
      case (Seq(), _) => Q(s, v)
      case (Seq(edge), _) => follow(s, edge, v, joinPoint)(Q)
      case (Seq(edge1, edge2), Some(newJoinPoint)) if
          s.moreJoins.id >= JoinMode.All.id &&
          // Can't directly match type because of type erasure ...
          edge1.isInstanceOf[ConditionalEdge[ast.Stmt, ast.Exp]] &&
          edge2.isInstanceOf[ConditionalEdge[ast.Stmt, ast.Exp]] &&
          // We only join branches that originate from if statements
          // this is the case if the source is a statement block,
          // as opposed to a loop head block.
          edge1.source.isInstanceOf[StatementBlock[ast.Stmt, ast.Exp]] &&
          edge2.source.isInstanceOf[StatementBlock[ast.Stmt, ast.Exp]] =>

        assert(edge1.source == edge2.source)

        val cedge1 = edge1.asInstanceOf[ConditionalEdge[ast.Stmt, ast.Exp]]
        val cedge2 = edge2.asInstanceOf[ConditionalEdge[ast.Stmt, ast.Exp]]

        // Here we assume that edge1.condition is the negation of edge2.condition.
        assert((cedge1.condition, cedge2.condition) match {
          case (exp1, ast.Not(exp2)) => exp1 == exp2
          case (ast.Not(exp1), exp2) => exp1 == exp2
          case _ => false
        })

        eval(s, cedge1.condition, pvef(cedge1.condition), v)((s1, t0, condNew, v1) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, v1, resetState = false)((s2, v2, QB) => {
            brancher.branch(s2, t0, (cedge1.condition, condNew), v2)(
              // Follow only until join point.
              (s3, v3) => follow(s3, edge1, v3, Some(newJoinPoint))((s, v) => QB(s, null, v)),
              (s3, v3) => follow(s3, edge2, v3, Some(newJoinPoint))((s, v) => QB(s, null, v))
            )
          })(entries => {
            val s2 = entries match {
              case Seq(entry) => // One branch is dead
                entry.s
              case Seq(entry1, entry2) => // Both branches are alive
                entry1.pathConditionAwareMerge(entry2, v1)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")
            }
            (s2, null)
          })((s4, _, v4) => {
            if (joinPoint.contains(newJoinPoint)) {
              Q(s4, v4)
            } else {
              // Continue after merging at join point.
              exec(s4, newJoinPoint, s4.methodCfg.inEdges(newJoinPoint).head.kind, v4, joinPoint)(Q)
            }
          })
        )

      case (Seq(thenEdge@ConditionalEdge(cond1, _, _, _), elseEdge@ConditionalEdge(cond2, _, _, _)), _)
        if Verifier.config.parallelizeBranches() && cond2 == ast.Not(cond1)() =>
        val condEdgeRecord = new ConditionalEdgeRecord(thenEdge.condition, s, v.decider.pcs)
        val sepIdentifier = v.symbExLog.openScope(condEdgeRecord)
        val res = eval(s, thenEdge.condition, IfFailed(thenEdge.condition), v)((s2, tCond, eCondNew, v1) =>
          brancher.branch(s2, tCond, (thenEdge.condition, eCondNew), v1)(
            (s3, v3) => {
              follow(s3, thenEdge, v3, joinPoint)(Q)
            },
            (s3, v3) => {
              follow(s3, elseEdge, v3, joinPoint)(Q)
            }))
        res

      case _ =>
        val uidBranchPoint = v.symbExLog.insertBranchPoint(edges.length)
        val res = edges.zipWithIndex.foldLeft(Success(): VerificationResult) {
          case (result: VerificationResult, (edge, edgeIndex)) => {
            if (edgeIndex != 0) {
              v.symbExLog.switchToNextBranch(uidBranchPoint)
            }
            v.symbExLog.markReachable(uidBranchPoint)
            result combine follow(s, edge, v, joinPoint)(Q)
          }
        }
        v.symbExLog.endBranchPoint(uidBranchPoint)
        res
>>>>>>> upstream/master
    }
  }

  def exec(s: State, graph: SilverCfg, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    exec(s, graph.entry, cfg.Kind.Normal, v, None)(Q)
  }

  def exec(s: State, block: SilverBlock, incomingEdgeKind: cfg.Kind.Value, v: Verifier, joinPoint: Option[SilverBlock])
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    block match {
      case cfg.StatementBlock(stmt) =>
        execs(s, stmt, v)((s1, v1) =>
<<<<<<< HEAD
          follows(s1, block, magicWandSupporter.getOutEdges(s1, block), IfFailed, v1)(Q))
=======
          follows(s1, magicWandSupporter.getOutEdges(s1, block), IfFailed, v1, joinPoint)(Q))
>>>>>>> upstream/master

      case   _: cfg.PreconditionBlock[ast.Stmt, ast.Exp]
           | _: cfg.PostconditionBlock[ast.Stmt, ast.Exp] =>

        /* It is expected that the CFG of a method *body* is executed, not that of
         * the whole method (which includes pre-/postcondition blocks).
         * See also the MethodSupporter.
         */
        sys.error(s"Unexpected block: $block")

<<<<<<< HEAD
      case block @ cfg.LoopHeadBlock(invs, stmts) =>
        // every loop should have exactly one invariant, which may be an And
        // we use the first invariant in invs because invs is a Seq[ast.Exp]
        // and a Seq may be mutable
        assert(invs.length == 1)
=======
      case block @ cfg.LoopHeadBlock(invs, stmts, _) =>
>>>>>>> upstream/master
        incomingEdgeKind match {
          case cfg.Kind.In =>
            /* We've reached a loop head block via an in-edge. Steps to perform:
             *   - Check loop invariant for self-framingness
             *   - Check that the loop guard is framed by the invariant
             *   - Exhale invariant of the target block
             *   - Push leftover state onto invariant context stack
             *   - Create state in which to execute the loop body by producing the
             *     invariant into an empty heap
             *   - Execute the statements in the loop head block
             *   - Follow the outgoing edges
             */
            val sepIdentifier = SymbExLogger.currentLog().openScope(
              new LoopInRecord(invs.head, s, v.decider.pcs))

            /* Havoc local variables that are assigned to in the loop body */
            val wvs = s.methodCfg.writtenVars(block)
              /* TODO: BUG: Variables declared by LetWand show up in this list, but shouldn't! */

            val gBody = Store(wvs.foldLeft(s.g.values)((map, x) => {
<<<<<<< HEAD
              /* 2025-01-29 Long:
               * havoc variables will get a new suffix and will not show up
               * in freshPositions, so we need to add them to freshPositions
               */
              val freshVar = v.decider.fresh(x)
              val existingTerm = map(x)
              /* if the variable cannot be found in freshPositions, it means
               * that it has not been assigned to yet
               */
              if (SymbExLogger.enabled && SymbExLogger.freshPositions.contains(existingTerm)) {
                SymbExLogger.freshPositions += freshVar -> SymbExLogger.freshPositions(existingTerm)
              }
              map.updated(x, freshVar)
            } ))
            val sBody = s.copy(isImprecise = false,
                               g = gBody,
                               h = Heap(),
                               optimisticHeap = Heap())
=======
              val xNew = v.decider.fresh(x)
              map.updated(x, xNew)}))
            val sBody = s.copy(g = gBody, h = Heap())
>>>>>>> upstream/master

            val edges = s.methodCfg.outEdges(block)
            val (outEdges, otherEdges) = edges partition(_.kind == cfg.Kind.Out)
            val sortedEdges = otherEdges ++ outEdges
            // extracts all the conditions from the edges (from the statements
            // that make them up?)
            //
            // keeps the unique ones
            val edgeConditions = sortedEdges.collect{case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => ce.condition}
                                            .distinct

            type PhaseData = (State, RecordedPathConditions, Set[FunctionDecl])
            var phase1data: Vector[PhaseData] = Vector.empty

            (executionFlowController.locally(sBody, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Check well-definedness of invariant")
                val mark = v0.decider.setPathConditionMark()

                wellformed(
                  s0.copy(loopPosition = Some(CheckPosition.Loop(invs, LoopPosition.Beginning))),
                  freshSnap,
                  invs,
                  ContractNotWellformed(viper.silicon.utils.ast.BigAnd(invs)),
                  v0)((s1, v1) => {   //pve is a placeholder
                  SymbExLogger.currentLog().closeScope(sepIdentifier)
                  val s1point5 = s1.copy(loopPosition = None)

                  // unset for at beginning of loop body
                  // produces into phase1data
                  phase1data = phase1data :+ (s1point5,
                                              v1.decider.pcs.after(mark),
<<<<<<< HEAD
                                              InsertionOrderedSet.empty[FunctionDecl] /*v2.decider.freshFunctions*/ /* [BRANCH-PARALLELISATION] */)
                  v1.decider.prover.comment("Loop head block: Check well-definedness of edge conditions")
                  edgeConditions.foldLeft(Success(): VerificationResult) {
                    case (fatalResult: FatalResult, _) => fatalResult
                    case (intermediateResult, eCond) =>
                      intermediateResult && executionFlowController.locally(s1point5, v1)((s2, v2) => {
                        eval(s2, eCond, WhileFailed(eCond), v2)((_, _, _) =>
                          Success())})}})})

            && executionFlowController.locally(s, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Establish invariant")
                consumes(s0.copy(loopPosition = Some(CheckPosition.Loop(invs, LoopPosition.Before))),
                  invs, LoopInvariantNotEstablished, v0)((sLeftover0, _, v1) => {
                  
                  var sLeftover1 = sLeftover0
                  if (isEquiImp(invs))
                    sLeftover1 = sLeftover0.copy(h = Heap(),
                      optimisticHeap = Heap(),
                      isImprecise = true)

                  val sLeftover = sLeftover1.copy(loopPosition = None)
                  
                  // unset enum for before loop in symbolic state here?
=======
                                              v1.decider.freshFunctions /* [BRANCH-PARALLELISATION] */)
                  Success()
                })})
            combine executionFlowController.locally(s, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Establish invariant")
                consumes(s0, invs, false, LoopInvariantNotEstablished, v0)((sLeftover, _, v1) => {
>>>>>>> upstream/master
                  v1.decider.prover.comment("Loop head block: Execute statements of loop head block (in invariant state)")

                  phase1data.foldLeft(Success(): VerificationResult) {
                    case (result, _) if !result.continueVerification => result
                    case (intermediateResult, (s1, pcs, ff1)) => /* [BRANCH-PARALLELISATION] ff1 */
<<<<<<< HEAD
                      val s2 = s1.copy(invariantContexts = (s0.isImprecise, sLeftover.isImprecise, sLeftover.h, sLeftover.optimisticHeap) +: s1.invariantContexts)
                      intermediateResult && executionFlowController.locally(s2, v1)((s3, v2) => {
  //                    v2.decider.declareAndRecordAsFreshFunctions(ff1 -- v2.decider.freshFunctions) /* [BRANCH-PARALLELISATION] */
                        v2.decider.assume(pcs.assumptions)
                        v2.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)
=======
                      val s2 = s1.copy(invariantContexts = sLeftover.h +: s1.invariantContexts)
                      intermediateResult combine executionFlowController.locally(s2, v1)((s3, v2) => {
                        v2.decider.declareAndRecordAsFreshFunctions(ff1 -- v2.decider.freshFunctions) /* [BRANCH-PARALLELISATION] */
                        v2.decider.assume(pcs.assumptions, Option.when(withExp)(DebugExp.createInstance("Loop invariant", pcs.assumptionExps)), false)
                        v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
>>>>>>> upstream/master
                        if (v2.decider.checkSmoke())
                          Success()
                        else {
                          execs(s3, stmts, v2)((s4, v3) => {
                            val edgeCondWelldefinedness = {
                              v1.decider.prover.comment("Loop head block: Check well-definedness of edge conditions")
                              edgeConditions.foldLeft(Success(): VerificationResult) {
                                case (result, _) if !result.continueVerification => result
                                case (intermediateResult, eCond) =>
                                  intermediateResult combine executionFlowController.locally(s4, v3)((s5, v4) => {
                                    eval(s5, eCond, WhileFailed(eCond), v4)((_, _, _, _) =>
                                      Success())
                                  })
                              }
                            }
                            v3.decider.prover.comment("Loop head block: Follow loop-internal edges")
<<<<<<< HEAD
                            follows(s4, block, sortedEdges, WhileFailed, v3)(Q)})}})}})}))
=======
                            edgeCondWelldefinedness combine follows(s4, sortedEdges, WhileFailed, v3, joinPoint)(Q)})}})}})}))
>>>>>>> upstream/master

          case _ =>
            /* We've reached a loop head block via an edge other than an in-edge: a normal edge or
             * and out-edge. We consider this edge to be a back-edge and we break the cycle by
             * attempting to re-establish the invariant.
             */
            v.decider.prover.comment("Loop head block: Re-establish invariant")
<<<<<<< HEAD
            // this is the consume at the end of the loop body
            
            val s0 = s.copy(loopPosition = Some(CheckPosition.Loop(invs, LoopPosition.End)))

            val edges = s0.methodCfg.outEdges(block)
            val (outEdges, otherEdges) = edges partition(_.kind == cfg.Kind.Out)
            val sortedEdges = otherEdges ++ outEdges
            // extracts all the conditions from the edges (from the statements
            // that make them up?)
            //
            // keeps the unique ones
            val edgeConditions =
              sortedEdges
                .collect{case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => ce.condition}
                .distinct
            
            // call eval on the loop condition to get checks for framing it if needed
            eval(s0, edgeConditions.head, IfFailed(edgeConditions.head), v)((_, _, _) => 
=======
            consumes(s, invs, false, e => LoopInvariantNotPreserved(e), v)((_, _, _) =>
>>>>>>> upstream/master
              Success())
            val sepIdentifier = SymbExLogger.currentLog().openScope(
              new LoopOutRecord(invs.head, s0, v.decider.pcs))
            // consume the loop invariant
            consumes(s0, invs, e => LoopInvariantNotPreserved(e), v)((s1, _, v1) => {
              SymbExLogger.currentLog().closeScope(sepIdentifier)
              val sepIdentifier2 = SymbExLogger.currentLog().openScope(
                new EndRecord(s1, v1.decider.pcs))
              SymbExLogger.currentLog().closeScope(sepIdentifier2)
              Success()})
        }
<<<<<<< HEAD

      case cfg.ConstrainingBlock(vars: Seq[ast.AbstractLocalVar @unchecked], body: SilverCfg) =>
        val arps = vars map (s.g.apply(_).asInstanceOf[Var])
        exec(s.setConstrainable(arps, true), body, v)((s1, v1) =>
          follows(s1.setConstrainable(arps, false), block, magicWandSupporter.getOutEdges(s1, block), Internal(_), v1)(Q))
=======
>>>>>>> upstream/master
    }
  }

  def execs(s: State, stmts: Seq[ast.Stmt], v: Verifier)
           (Q: (State, Verifier) => VerificationResult)
           : VerificationResult =

    if (stmts.nonEmpty)
      exec(s, stmts.head, v)((s1, v1) =>
        execs(s1, stmts.tail, v1)(Q))
    else
      Q(s, v)

  def exec(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {
    val sepIdentifier = v.symbExLog.openScope(new ExecuteRecord(stmt, s, v.decider.pcs))
    exec2(s, stmt, v)((s1, v1) => {
      v1.symbExLog.closeScope(sepIdentifier)
      Q(s1, v1)})
  }

  def exec2(state: State, stmt: ast.Stmt, v: Verifier)
           (continuation: (State, Verifier) => VerificationResult)
           : VerificationResult = {

    val s = state.copy(h = magicWandSupporter.getExecutionHeap(state))
    val Q: (State, Verifier) => VerificationResult = (s, v) => {
      continuation(magicWandSupporter.moveToReserveHeap(s, v), v)}

    /* For debugging-purposes only */
    stmt match {
      case _: ast.Seqn =>
      case _ =>
        v.logger.debug(s"\nEXECUTE ${viper.silicon.utils.ast.sourceLineColumn(stmt)}: $stmt")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        v.decider.prover.comment("[exec]")
        v.decider.prover.comment(stmt.toString())
    }

    val executed = stmt match {
      case ast.Seqn(stmts, _) =>
        execs(s, stmts, v)(Q)

      /*
      case ast.Label(name, _) =>
        val s1 = s.copy(oldHeaps = s.oldHeaps + (name -> magicWandSupporter.getEvalHeap(s)))
        Q(s1, v)
      */

      case ast.LocalVarDeclStmt(decl) =>
        val x = decl.localVar
        val (t, newExp) = v.decider.fresh(x)
        Q(s.copy(g = s.g + (x -> (t, newExp))), v)

      case ass @ ast.LocalVarAssign(x, rhs) =>
<<<<<<< HEAD
        eval(s, rhs, AssignmentFailed(ass), v)((s1, tRhs, v1) => {
          val t = ssaifyRhs(tRhs, x.name, x.typ, v, ass.pos)
          Q(s1.copy(g = s1.g + (x, t)), v1)
        })
=======
        eval(s, rhs, AssignmentFailed(ass), v)((s1, tRhs, rhsNew, v1) => {
          val (t, e) = ssaifyRhs(tRhs, rhs, rhsNew, x.name, x.typ, v, s1)
          Q(s1.copy(g = s1.g + (x, (t, e))), v1)})
>>>>>>> upstream/master

      /* TODO: Encode assignments e1.f := e2 as
       *         exhale acc(e1.f)
       *         inhale acc(e1.f) && e1.f == e2
       *       and benchmark possible performance effects.
       */

      /* Assignment for a field that contains quantified chunks */
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
        if s.qpFields.contains(field) => sys.error(s"Quantified permissions not supported for the field in (${stmt.getClass.getName}): $stmt")
      /*
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
              if s.qpFields.contains(field) =>

        assert(!s.exhaleExt)
        val pve = AssignmentFailed(ass)
        eval(s, eRcvr, pve, v)((s1, tRcvr, eRcvrNew, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, _, v2) => {
            val (relevantChunks, otherChunks) =
              quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s2.h, BasicChunkIdentifier(field.name))
            val hints = quantifiedChunkSupporter.extractHints(None, Seq(tRcvr))
            val chunkOrderHeuristics = quantifiedChunkSupporter.singleReceiverChunkOrderHeuristic(Seq(tRcvr), hints, v2)
            val s2p = if (s2.heapDependentTriggers.contains(field)){
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, field, Seq(`?r`), relevantChunks, v1)
              val debugExp = Option.when(withExp)(DebugExp.createInstance(s"Field Trigger: (${eRcvrNew.toString()}).${field.name}"))
              v2.decider.assume(FieldTrigger(field.name, smDef1.sm, tRcvr), debugExp)
              s2.copy(smCache = smCache1)
            } else {
              s2
            }
            v2.decider.clearModel()
            val result = quantifiedChunkSupporter.removePermissions(
              s2p,
              relevantChunks,
              Seq(`?r`),
              Option.when(withExp)(Seq(ast.LocalVarDecl(`?r`.id.name, ast.Ref)())),
              `?r` === tRcvr,
              eRcvrNew.map(r => ast.EqCmp(ast.LocalVar(`?r`.id.name, ast.Ref)(), r)()),
              Some(Seq(tRcvr)),
              field,
              FullPerm,
              Option.when(withExp)(ast.FullPerm()()),
              chunkOrderHeuristics,
              v2
            )
            result match {
              case (Complete(), s3, remainingChunks) =>
                val h3 = Heap(remainingChunks ++ otherChunks)
                val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s3, field, Seq(tRcvr), tRhs, v2)
                v1.decider.prover.comment("Definitional axioms for singleton-FVF's value")
<<<<<<< HEAD
                v1.decider.assume(smValueDef)
                val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), field, Seq(tRcvr), FullPerm(), sm)
                v1.decider.assume(FieldTrigger(field.name, sm, tRcvr))
                Q(s3.copy(h = h3 + ch), v2)
              case (Incomplete(_), s3, _) =>
                createFailure(pve dueTo InsufficientPermission(fa), v2, s3)}}))
*/
=======
                val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-FVF's value", isInternal_ = true))
                v1.decider.assumeDefinition(smValueDef, debugExp)
                val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)(ass.pos, ass.info, ass.errT))),
                  field, Seq(tRcvr), Option.when(withExp)(Seq(eRcvrNew.get)), FullPerm, Option.when(withExp)(ast.FullPerm()(ass.pos, ass.info, ass.errT)), sm, s.program)
                if (s3.heapDependentTriggers.contains(field)) {
                  val debugExp2 = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvrNew.toString()}.${field.name})"))
                  v1.decider.assume(FieldTrigger(field.name, sm, tRcvr), debugExp2)
                }
                val s4 = s3.copy(h = h3 + ch)
                val (debugHeapName, _) = v.getDebugOldLabel(s4, fa.pos)
                val s5 = if (withExp) s4.copy(oldHeaps = s4.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s4))) else s4
                Q(s5, v2)
              case (Incomplete(_, _), s3, _) =>
                createFailure(pve dueTo InsufficientPermission(fa), v2, s3, "sufficient permission")}}))
>>>>>>> upstream/master

      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs) =>
       
        assert(!s.exhaleExt)
        val pve = AssignmentFailed(ass)
<<<<<<< HEAD

        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) => {
            val fap = ast.FieldAccessPredicate(fa, ast.FullPerm()(ass.pos))(ass.pos)

            consume(s2, fap, pve, v2)((s3, snap, v3) => {

              // TODO;EXTRA CHECK ISSUE(S): We assume the Ref is !== null here
              v3.decider.assume(tRcvr !== Null())
              val tSnap = ssaifyRhs(tRhs, field.name, field.typ, v3, ass.pos)
              val id = BasicChunkIdentifier(field.name)
              val newChunk = BasicChunk(FieldID, id, Seq(tRcvr), tSnap, FullPerm())

              chunkSupporter.produce(s3, s3.h, newChunk, v3)((s4, h4, v4) => {
              Q(s4.copy(h = h4), v4)})
=======
        eval(s, eRcvr, pve, v)((s1, tRcvr, eRcvrNew, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, rhsNew, v2) => {
            val resource = fa.res(s.program)
            val ve = pve dueTo InsufficientPermission(fa)
            val description = s"consume ${ass.pos}: $ass"
            chunkSupporter.consume(s2, s2.h, resource, Seq(tRcvr), eRcvrNew.map(Seq(_)), FullPerm, Option.when(withExp)(ast.FullPerm()(ass.pos, ass.info, ass.errT)), false, ve, v2, description)((s3, h3, _, v3) => {
              val (tSnap, _) = ssaifyRhs(tRhs, rhs, rhsNew, field.name, field.typ, v3, s3)
              val id = BasicChunkIdentifier(field.name)
              val newChunk = BasicChunk(FieldID, id, Seq(tRcvr), eRcvrNew.map(Seq(_)), tSnap, rhsNew, FullPerm, Option.when(withExp)(ast.FullPerm()(ass.pos, ass.info, ass.errT)))
              chunkSupporter.produce(s3, h3, newChunk, v3)((s4, h4, v4) => {
                val s5 = s4.copy(h = h4)
                val (debugHeapName, _) = v4.getDebugOldLabel(s5, fa.pos)
                val s6 = if (withExp) s5.copy(oldHeaps = s5.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s5))) else s5
                Q(s6, v4)
              })
>>>>>>> upstream/master
            })
          })
        )

      case stmt@ast.NewStmt(x, fields) =>
        val (tRcvr, eRcvrNew) = v.decider.fresh(x)
        val debugExp = Option.when(withExp)(ast.NeCmp(x, ast.NullLit()())())
        val debugExpSubst = Option.when(withExp)(ast.NeCmp(eRcvrNew.get, ast.NullLit()())())
        val (debugHeapName, debugLabel) = v.getDebugOldLabel(s, stmt.pos)
        v.decider.assume(tRcvr !== Null, debugExp, debugExpSubst)
        val newChunks = fields map (field => {
          val p = FullPerm
          val pExp = Option.when(withExp)(ast.FullPerm()(stmt.pos, stmt.info, stmt.errT))
          val snap = v.decider.fresh(field.name, v.symbolConverter.toSort(field.typ), Option.when(withExp)(extractPTypeFromExp(x)))
          val snapExp = Option.when(withExp)(ast.DebugLabelledOld(ast.FieldAccess(eRcvrNew.get, field)(), debugLabel)(stmt.pos, stmt.info, stmt.errT))
          if (s.qpFields.contains(field)) {
            val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, field, Seq(tRcvr), snap, v)
            v.decider.prover.comment("Definitional axioms for singleton-FVF's value")
            val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-FVF's value", isInternal_ = true))
            v.decider.assumeDefinition(smValueDef, debugExp)
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)(stmt.pos, stmt.info, stmt.errT))),
              field, Seq(tRcvr), Option.when(withExp)(Seq(eRcvrNew.get)), p, pExp, sm, s.program)
          } else {
            BasicChunk(FieldID, BasicChunkIdentifier(field.name), Seq(tRcvr), Option.when(withExp)(Seq(x)), snap, snapExp, p, pExp)
          }
        })
        val ts = viper.silicon.state.utils.computeReferenceDisjointnesses(s, tRcvr)
        val esNew = eRcvrNew.map(rcvr => BigAnd(viper.silicon.state.utils.computeReferenceDisjointnessesExp(s, rcvr)))
        val s1 = s.copy(g = s.g + (x, (tRcvr, eRcvrNew)), h = s.h + Heap(newChunks))
        val s2 = if (withExp) s1.copy(oldHeaps = s1.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s1))) else s1
        v.decider.assume(ts, Option.when(withExp)(DebugExp.createInstance(Some("Reference Disjointness"), esNew, esNew, InsertionOrderedSet.empty)), enforceAssumption = false)
        Q(s2, v)

      // commenting this out causes disjunction_fast to fail
      // also I think we have a problem with error messages
      /*
      case inhale @ ast.Inhale(a) => a match {
        case _: ast.FalseLit =>
          Success()
        case _ =>
          produce(s, freshSnap, a, InhaleFailed(inhale), v)((s1, v1) => {
            v1.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterInhale)
            Q(s1, v1)})
      }

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(s, a, false, pve, v)((s1, _, v1) =>
          Q(s1, v1))
<<<<<<< HEAD
      */
      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        a match {
          /* "assert true" triggers a heap compression. */
          case _: ast.TrueLit =>
            val s1 = stateConsolidator.consolidate(s, v)
            Q(s1, v)

          /* "assert false" triggers a smoke check. If successful, we backtrack. */
          case _: ast.FalseLit =>
            executionFlowController.tryOrFail0(s.copy(h = magicWandSupporter.getEvalHeap(s)), v)((s1, v1, QS) => {
              if (v1.decider.checkSmoke())
                QS(s1.copy(h = s.h), v1)
              else
                createFailure(pve dueTo AssertionFalse(a), v1, s1)
            })((_, _) => Success())

          case _ =>
            if (Verifier.config.disableSubsumption()) {
              //This case resembles what's written in the PhD thesis
              consume(s, a, pve, v)((s1, snap1, v1) =>
                wellformed(s1.copy(isImprecise = true), freshSnap, Seq(a), pve, v1)((s2, v2) =>
                  Q(s, v2))
              )
            } else if (s.exhaleExt) {
              Predef.assert(s.h.values.isEmpty)
              Predef.assert(s.reserveHeaps.head.values.isEmpty)

              /* When exhaleExt is set magicWandSupporter.transfer is used to transfer permissions to
               * hUsed (reserveHeaps.head) instead of consuming them. hUsed is later discarded and replaced
               * by s.h. By copying hUsed to s.h the contained permissions remain available inside the wand.
               */
              consume(s, a, pve, v)((s1, snap1, v1) => {
                wellformed(s1.copy(isImprecise = true), freshSnap, Seq(a), pve, v1)((s2, v2) =>
                  Q(s2.copy(isImprecise = s.isImprecise, h = s2.reserveHeaps.head, optimisticHeap = s.optimisticHeap), v2))
              })
            } else {
              consume(s, a, pve, v)((s1, snap1, v1) => {
                wellformed(s1.copy(isImprecise = true), freshSnap, Seq(a), pve, v1)((s2, v2) => {
                  val s3 = s2.copy(isImprecise = s.isImprecise, h = s.h, optimisticHeap = s.optimisticHeap, reserveHeaps = s.reserveHeaps)
                  Q(s3, v2)
                })
              })
            }
        }

      // TODO;BRANCH POSITIONING: what is this?
      // A call havoc_all_R() results in Silicon efficiently havocking all instances of resource R.
=======

      case assert @ ast.Assert(a: ast.FalseLit) if !s.isInPackage =>
        /* "assert false" triggers a smoke check. If successful, we backtrack. */
        executionFlowController.tryOrFail0(s.copy(h = magicWandSupporter.getEvalHeap(s)), v)((s1, v1, QS) => {
          if (v1.decider.checkSmoke(true))
            QS(s1.copy(h = s.h), v1)
          else
            createFailure(AssertFailed(assert) dueTo AssertionFalse(a), v1, s1, False, true, Option.when(withExp)(a))
        })((_, _) => Success())

      case assert @ ast.Assert(a) if Verifier.config.disableSubsumption() =>
        val r =
          consume(s, a, false, AssertFailed(assert), v)((_, _, _) =>
            Success())

        r combine Q(s, v)

      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        if (s.exhaleExt) {
          Predef.assert(s.h.values.isEmpty)
          Predef.assert(s.reserveHeaps.head.values.isEmpty)

          /* When exhaleExt is set magicWandSupporter.transfer is used to transfer permissions to
           * hUsed (reserveHeaps.head) instead of consuming them. hUsed is later discarded and replaced
           * by s.h. By copying hUsed to s.h the contained permissions remain available inside the wand.
           */
          consume(s, a, false, pve, v)((s2, _, v1) => {
            Q(s2.copy(h = s2.reserveHeaps.head), v1)
          })
        } else
          consume(s, a, false, pve, v)((s1, _, v1) => {
            val s2 = s1.copy(h = s.h, reserveHeaps = s.reserveHeaps)
            Q(s2, v1)})

      // Calling hack407_R() results in Silicon efficiently havocking all instances of resource R.
>>>>>>> upstream/master
      // See also Silicon issue #407.
      case call @ ast.MethodCall(methodName, _, _)
        if !Verifier.config.disableHavocHack407() && methodName.startsWith(hack407_method_name_prefix) => {

        sys.error("Do not use havoc_all_R(); it is not supported by Gradual Silicon! Aborting safely...")

        val resourceName = methodName.stripPrefix(hack407_method_name_prefix)
        val member = s.program.collectFirst {
          case m: ast.Field if m.name == resourceName => m
          case m: ast.Predicate if m.name == resourceName => m
        }.getOrElse(sys.error(s"Found $methodName, but no matching field or predicate $resourceName"))
        val h1 = Heap(s.h.values.map {
          case bc: BasicChunk if bc.id.name == member.name =>
            bc.withSnap(freshSnap(bc.snap.sort, v), None)
          case qfc: QuantifiedFieldChunk if qfc.id.name == member.name =>
            qfc.withSnapshotMap(freshSnap(qfc.fvf.sort, v))
          case qpc: QuantifiedPredicateChunk if qpc.id.name == member.name =>
            qpc.withSnapshotMap(freshSnap(qpc.psf.sort, v))
          case other =>
            other
        })
        Q(s.copy(h = h1), v)

<<<<<<< HEAD
      }
=======
      // Calling hack510() triggers a state consolidation.
      // See also Silicon issue #510.
      case ast.MethodCall(`hack510_method_name`, _, _) =>
        val s1 = v.stateConsolidator(s).consolidate(s, v)
        Q(s1, v)
>>>>>>> upstream/master

      case call @ ast.MethodCall(methodName, eArgs, lhs) =>
        val meth = s.program.findMethod(methodName)
        val fargs = meth.formalArgs.map(_.localVar)
        val formalsToActuals: Map[ast.LocalVar, ast.Exp] = fargs.zip(eArgs).to(Map)
        val reasonTransformer = (n: viper.silver.verifier.errors.ErrorNode) => n.replace(formalsToActuals)
<<<<<<< HEAD
        val pveCall = CallFailed(call).withReasonNodeTransformed(reasonTransformer)
=======
        val pveCall = CallFailed(call)
        val pveCallTransformed = pveCall.withReasonNodeTransformed(reasonTransformer)
>>>>>>> upstream/master

        val mcLog = new MethodCallRecord(call, s, v.decider.pcs)
        val sepIdentifier = v.symbExLog.openScope(mcLog)
        val paramLog = new CommentRecord("Parameters", s, v.decider.pcs)
<<<<<<< HEAD
        val paramId = currentLog.openScope(paramLog)
        evals(s, eArgs, _ => pveCall, v)((s1, tArgs, v1) => {
          currentLog.closeScope(paramId)
=======
        val paramId = v.symbExLog.openScope(paramLog)
        evals(s, eArgs, _ => pveCall, v)((s1, tArgs, eArgsNew, v1) => {
          v1.symbExLog.closeScope(paramId)
>>>>>>> upstream/master
          val exampleTrafo = CounterexampleTransformer({
            case ce: SiliconCounterexample => ce.withStore(s1.g)
            case ce => ce
          })
          val pvePre = ErrorWrapperWithExampleTransformer(PreconditionInCallFalse(call).withReasonNodeTransformed(reasonTransformer), exampleTrafo)
          val preCondLog = new CommentRecord("Precondition", s1, v1.decider.pcs)
<<<<<<< HEAD
          val preCondId = currentLog.openScope(preCondLog)
          // TODO: Fix this
          reconstructedPermissions.addMethodCallStatement(call,
            new Translator(s1, v1.decider.pcs).getAccessibilityPredicates,
            zip3(v1.decider.pcs.branchConditionsOrigins.map(entry => Null()),
              v1.decider.pcs.branchConditionsAstNodes,
              v1.decider.pcs.branchConditionsOrigins))

          // this is run unconditionally (or so it seems), so we can attach the
          // method call ast node here
          
          val s2 = s1.copy(g = Store(fargs.zip(tArgs)),
            oldStore = Some(s1.g),
            oldHeaps = s1.oldHeaps + (Verifier.PRE_HEAP_LABEL -> Heap()) + (Verifier.PRE_OPTHEAP_LABEL -> Heap()),
            recordVisited = true,
            methodCallAstNode = Some(call))

          consumes(s2, meth.pres, _ => pvePre, v1)((s3, _, v2) => {
            currentLog.closeScope(preCondId)
=======
          val preCondId = v1.symbExLog.openScope(preCondLog)
          val argsWithExp = if (withExp)
            tArgs zip (eArgsNew.get.map(Some(_)))
          else
            tArgs zip Seq.fill(tArgs.size)(None)
          val s2 = s1.copy(g = Store(fargs.zip(argsWithExp)),
                           recordVisited = true)
          consumes(s2, meth.pres, false, _ => pvePre, v1)((s3, _, v2) => {
            v2.symbExLog.closeScope(preCondId)
>>>>>>> upstream/master
            val postCondLog = new CommentRecord("Postcondition", s3, v2.decider.pcs)
            val postCondId = v2.symbExLog.openScope(postCondLog)
            val outs = meth.formalReturns.map(_.localVar)
            val gOuts = Store(outs.map(x => (x, v2.decider.fresh(x))).toMap)
<<<<<<< HEAD
            val outOldStore = Store(lhs.zip(outs).map(p => (p._1, gOuts(p._2))).toMap)
            var s4p = s3

            if (isEquiImp(meth.pres))
              s4p = s3.copy(h = Heap(),
                optimisticHeap = Heap(),
                isImprecise = true)

            val s4 = s4p.copy(g = s3.g + gOuts,
              oldStore = Some(s1.g + outOldStore),
              oldHeaps = s3.oldHeaps + (Verifier.PRE_STATE_LABEL -> s1.h) + (Verifier.PRE_HEAP_LABEL -> s1.h) + (Verifier.PRE_OPTHEAP_LABEL -> s1.optimisticHeap))
            produces(s4, freshSnap, meth.posts, _ => pveCall, v2)((s5, v3) => {
              // we MUST unset both oldStore and the methodCallAstNode once we
              // are done with the method call
              val s6 = s5.copy(oldStore = None, methodCallAstNode = None)

              currentLog.closeScope(postCondId)

              v3.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)

              val gLhs = Store(lhs.zip(outs)
                .map(p => (p._1, s6.g(p._2))).toMap)

              val s7 = s6.copy(g = s1.g + gLhs,
                oldHeaps = s1.oldHeaps,
                recordVisited = s1.recordVisited)

              currentLog.closeScope(sepIdentifier)

              Q(s7, v3)
            })
          })
        })
=======
            val s4 = s3.copy(g = s3.g + gOuts, oldHeaps = s3.oldHeaps + (Verifier.PRE_STATE_LABEL -> magicWandSupporter.getEvalHeap(s1)))
            produces(s4, freshSnap, meth.posts, _ => pveCallTransformed, v2)((s5, v3) => {
              v3.symbExLog.closeScope(postCondId)
              v3.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
              val gLhs = Store(lhs.zip(outs)
                              .map(p => (p._1, s5.g.values(p._2))).toMap)
              val s6 = s5.copy(g = s1.g + gLhs,
                               oldHeaps = s1.oldHeaps,
                               recordVisited = s1.recordVisited)
              v3.symbExLog.closeScope(sepIdentifier)
              Q(s6, v3)})})})
>>>>>>> upstream/master

      case fold @ ast.Fold(pap @ ast.PredicateAccessPredicate(predAcc @ ast.PredicateAccess(eArgs, predicateName), _)) =>
        assert(s.constrainableARPs.isEmpty)
        v.decider.startDebugSubExp()
        val ePerm = pap.perm
        val predicate = s.program.findPredicate(predicateName)
        val pve = FoldFailed(fold)
<<<<<<< HEAD
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            v2.decider.assertgv(s2.isImprecise, IsPositive(tPerm)) { //The IsPositive check is redundant
              case true =>
                val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                predicateSupporter.fold(s2, predicate, Some(fold), tArgs, tPerm, wildcards, pve, v2)(Q)
              case false =>
                createFailure(pve dueTo NegativePermission(ePerm), v2, s2)
            } match {
              case (verificationResult, _) => verificationResult
            }
          }))
=======
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, ePermNew, v2) =>
            permissionSupporter.assertPositive(s2, tPerm, if (withExp) ePermNew.get else ePerm, pve, v2)((s3, v3) => {
              val wildcards = s3.constrainableARPs -- s1.constrainableARPs
              predicateSupporter.fold(s3, predicate, tArgs, eArgsNew, tPerm, ePermNew, wildcards, pve, v3)((s4, v4) => {
                  v3.decider.finishDebugSubExp(s"folded ${predAcc.toString}")
                  Q(s4, v4)
                }
              )})))
>>>>>>> upstream/master

      case unfold @ ast.Unfold(pap @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), _)) =>
        assert(s.constrainableARPs.isEmpty)
        v.decider.startDebugSubExp()
        val ePerm = pap.perm
        val predicate = s.program.findPredicate(predicateName)
        val pve = UnfoldFailed(unfold)
<<<<<<< HEAD
        val sFrame = s.copy(gatherFrame = true)
        evals(sFrame, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1.copy(gatherFrame = false), ePerm, pve, v1)((s2, tPerm, v2) => {
=======
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, ePermNew, v2) => {
>>>>>>> upstream/master

            val smCache1 = if (s2.qpPredicates.contains(predicate) && s2.heapDependentTriggers.contains(predicate)) {
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s2.h, BasicChunkIdentifier(predicateName))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v2)
              val eArgsStr = eArgsNew.mkString(", ")
              val debugExp = Option.when(withExp)(DebugExp.createInstance(Some(s"PredicateTrigger(${predicate.name}($eArgsStr))"), Some(pa),
                Some(ast.PredicateAccess(eArgsNew.get, predicateName)(pa.pos, pa.info, pa.errT)), None, isInternal_ = true, InsertionOrderedSet.empty))
              v2.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs), debugExp)
              smCache1
            } else {
              s2.smCache
            }

<<<<<<< HEAD
            v2.decider.assertgv(s2.isImprecise, IsPositive(tPerm)) { //The IsPositive check is redundant
              case true =>
                val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                predicateSupporter.unfold(s2.copy(smCache = smCache1), predicate, Some(unfold), tArgs, tPerm, wildcards, pve, v2, pa)(Q)
              case false =>
                createFailure(pve dueTo NegativePermission(ePerm), v2, s2)
            } match {
              case (verificationResult, _) => verificationResult
            }
=======
            permissionSupporter.assertPositive(s2, tPerm, if (withExp) ePermNew.get else ePerm, pve, v2)((s3, v3) => {
              val wildcards = s3.constrainableARPs -- s1.constrainableARPs
              predicateSupporter.unfold(s3.copy(smCache = smCache1), predicate, tArgs, eArgsNew, tPerm, ePermNew, wildcards, pve, v3, pa)(
                (s4, v4) => {
                  v2.decider.finishDebugSubExp(s"unfolded ${pa.toString}")
                  Q(s4, v4)
                })
            })
>>>>>>> upstream/master
          }))

      /*
      case pckg @ ast.Package(wand, proofScript) =>
        val pve = PackageFailed(pckg)
          magicWandSupporter.packageWand(s.copy(isInPackage = true), wand, proofScript, pve, v)((s1, chWand, v1) => {

            val hOps = s1.reserveHeaps.head + chWand
            assert(s.exhaleExt || s1.reserveHeaps.length == 1)
            val s2 =
              if (s.exhaleExt) {
                s1.copy(h = Heap(),
                        exhaleExt = true,
                         * It is assumed, that s.reserveHeaps.head (hUsed) is not used or changed
                         * by the packageWand method. hUsed is normally used during transferring
                         * consume to store permissions that have already been consumed. The
                         * permissions on this heap should be discarded after a statement finishes
                         * execution. hUsed should therefore be empty unless the package statement
                         * was triggered by heuristics during a consume operation.
                         *
                        reserveHeaps = s.reserveHeaps.head +: hOps +: s1.reserveHeaps.tail)
              } else {
                * c1.reserveHeap is expected to be [σ.h'], i.e. the remainder of σ.h *
                s1.copy(h = hOps,
                        exhaleExt = false,
                        reserveHeaps = Nil)
              }
            assert(s2.reserveHeaps.length == s.reserveHeaps.length)

            val smCache3 = chWand match {
              case ch: QuantifiedMagicWandChunk if s2.heapDependentTriggers.contains(MagicWandIdentifier(wand, s2.program)) =>
                val (relevantChunks, _) =
                  quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s2.h, ch.id)
                val bodyVars = wand.subexpressionsToEvaluate(s.program)
                val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v1.symbolConverter.toSort(bodyVars(i).typ), false))
                val (smDef, smCache) =
                  quantifiedChunkSupporter.summarisingSnapshotMap(
                    s2, wand, formalVars, relevantChunks, v1)
                v1.decider.assume(PredicateTrigger(ch.id.toString, smDef.sm, ch.singletonArgs.get),
                  Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${ch.id.toString}(${ch.singletonArgExps.get}))", isInternal_ = true)))
                smCache
              case _ => s2.smCache
            }

            continuation(s2.copy(smCache = smCache3, isInPackage = s.isInPackage), v1)
          })

      case apply @ ast.Apply(e) =>
        val pve = ApplyFailed(apply)
        magicWandSupporter.applyWand(s, e, pve, v)(Q)
<<<<<<< HEAD
*/
=======

      case havoc: ast.Quasihavoc =>
        havocSupporter.execHavoc(havoc, v, s)(Q)

      case havocall: ast.Quasihavocall =>
        havocSupporter.execHavocall(havocall, v, s)(Q)

      case viper.silicon.extensions.TryBlock(body) =>
        var bodySucceeded = false
        val bodyResult = exec(s, body, v)((s1, v2) => {
          bodySucceeded = true
          Q(s1, v2)
        })
        if (bodySucceeded) bodyResult
        else Q(s, v)

>>>>>>> upstream/master
      /* These cases should not occur when working with the CFG-representation of the program. */
      case _: ast.Goto
           | _: ast.If
           | _: ast.Label
           | _: ast.Seqn
           | _: ast.Assume
           | _: ast.ExtensionStmt
           | _: ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")

      /* These cases were commented out, because they are not supported by Silicon-gv. */
      case _: ast.Inhale
           | _: ast.Exhale
           | _: ast.Package
           | _: ast.Apply => createFailure(createUnexpectedNodeError(stmt,""), v, s)
    }

    executed
  }

<<<<<<< HEAD
   private def ssaifyRhs(rhs: Term, name: String, typ: ast.Type, v: Verifier, pos: ast.Position): Term = {
     rhs match {
       /* 2025-01-29 Long:
        * The following line used to be
        * case _: Var | _: Literal =>
        */
       case _: Literal =>
         rhs
=======
   private def ssaifyRhs(rhs: Term, rhsExp: ast.Exp, rhsExpNew: Option[ast.Exp], name: String, typ: ast.Type, v: Verifier, s : State): (Term, Option[ast.Exp]) = {
     rhs match {
       case _: Var | _: Literal =>
         (rhs, rhsExpNew)
>>>>>>> upstream/master

       case _  =>
         /* 2018-06-05 Malte:
          *   This case was previously guarded by the condition
          *     rhs.existsDefined {
          *       case t if v.triggerGenerator.isForbiddenInTrigger(t) => true
          *     }
          *   and followed by a catch-all case in which rhs was returned.
          *   However, reducing the number of fresh symbols does not appear to improve
          *   performance; instead, it can cause an exponential blow-up in term size, as
          *   reported by Silicon issue #328.
          */
<<<<<<< HEAD
         val t = v.decider.fresh(name, v.symbolConverter.toSort(typ))
         v.decider.assume(t === rhs)
         /* 2025-01-29 Long:
          * record position where the Var was freshened in freshPositions
          * freshPositions should not contain this Var yet
          */
         if (SymbExLogger.enabled) {
           SymbExLogger.freshPositions += t -> pos
         }

         t
=======
         val t = v.decider.fresh(name, v.symbolConverter.toSort(typ), Option.when(withExp)(extractPTypeFromExp(rhsExp)))
         val (eNew, debugExp) = if (withExp) {
           val eRhs = rhsExp
           val eNew = ast.LocalVarWithVersion(simplifyVariableName(t.id.name), typ)(eRhs.pos, eRhs.info, eRhs.errT)
           val exp = ast.EqCmp(ast.LocalVar(name, typ)(), eRhs)(eRhs.pos, eRhs.info, eRhs.errT)
           val expNew = ast.EqCmp(eNew, rhsExpNew.get)()
           val debugExp = DebugExp.createInstance(exp, expNew)
           (Some(eNew), Some(debugExp))
         } else {
            (None, None)
         }
         v.decider.assumeDefinition(BuiltinEquals(t, rhs), debugExp)
         (t, eNew)
>>>>>>> upstream/master
     }
   }

  private val hack407_method_name_prefix = "___silicon_hack407_havoc_all_"

  def hack407_havoc_all_resources_method_name(id: String): String = s"$hack407_method_name_prefix$id"

  def hack407_havoc_all_resources_method_call(id: String): ast.MethodCall = {
    ast.MethodCall(
      methodName = hack407_havoc_all_resources_method_name(id),
      args = Vector.empty,
      targets = Vector.empty
    )(ast.NoPosition, ast.NoInfo, ast.NoTrafos)
  }

  private val hack510_method_name = "___silicon_hack510_consolidate_state"
}
