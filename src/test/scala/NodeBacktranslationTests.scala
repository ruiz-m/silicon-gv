// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

<<<<<<< HEAD
import org.scalatest.FunSuite
=======
import org.scalatest.funsuite.AnyFunSuite
>>>>>>> upstream/master
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.Failure

<<<<<<< HEAD
class NodeBacktranslationTests extends FunSuite {
  // These two tests rely on functions and exhale
/*  test("Issue #348 Test 1") {
=======
class NodeBacktranslationTests extends AnyFunSuite {
  test("Issue #348 Test 1") {
>>>>>>> upstream/master
    runTest("errorMessageTests/misc/", "0348-1", tests.instantiateFrontend())
  }

  test("Issue #348 Test 2") {
    runTest("errorMessageTests/misc/", "0348-2", tests.instantiateFrontend())
<<<<<<< HEAD
  } */
=======
  }
>>>>>>> upstream/master

  def runTest(filePrefix: String, fileName: String, frontend: SilFrontend): Unit = {
    val program = tests.loadProgram(filePrefix, fileName, frontend)

    val method = program.methods.head
    val body = method.body.get
    val exhale = body.ss.last.asInstanceOf[Exhale]

    val assignments: Map[LocalVar, Exp] =
      method.deepCollectInBody { case lva: LocalVarAssign => lva }
<<<<<<< HEAD
            .map(lva => lva.lhs -> lva.rhs)(collection.breakOut)
=======
            .map(lva => lva.lhs -> lva.rhs)
            .to(Map)
>>>>>>> upstream/master

    val backtranslationTransformer = ViperStrategy.Slim({
      case lv: LocalVar if assignments.contains(lv) =>
        val (pos, info, _) = lv.getPrettyMetadata
        /* Note: lv might already have an error transformer set. It will be replaced. */
<<<<<<< HEAD
        lv.meta = (pos, info, NodeTrafo(assignments(lv)))
    })
=======
        lv.withMeta(pos, info, NodeTrafo(assignments(lv)))
    }).forceCopy() // TODO: Rewriting is forced because changes in metadata are irrelevant for comparison operator, but a cleaner solution should be found
>>>>>>> upstream/master

    val substitutionTransformer = ViperStrategy.Slim({
      case lv: LocalVar if assignments.contains(lv) => assignments(lv)
    })

<<<<<<< HEAD
    // TODO: Rewriting is forced because changes in metadata are irrelevant for comparison operator, but a cleaner solution should be found
    ViperStrategy.forceRewrite = true
    val exhaleToVerify = backtranslationTransformer.execute[Exhale](exhale)
    ViperStrategy.forceRewrite = false
=======
    val exhaleToVerify = backtranslationTransformer.execute[Exhale](exhale)
>>>>>>> upstream/master
    val exhaleToReport = substitutionTransformer.execute[Exhale](exhale)

    assert(exhaleToVerify.toString == exhale.toString, "Unexpected syntactic difference")

    val bodyToVerify = body.copy(body.ss.init :+ exhaleToVerify)(body.pos, body.info, body.errT)
    val methodToVerify = method.copy(body = Some(bodyToVerify))(method.pos, method.info, method.errT)
    val programToVerify = program.copy(methods = Seq(methodToVerify))(program.pos, program.info, program.errT)

    val error = tests.verifyProgram(programToVerify, frontend).asInstanceOf[Failure].errors.head

    assert(
      error.readableMessage.contains(s"Assertion ${exhaleToReport.exp}"),
      "Expected error text not found")
  }
}
