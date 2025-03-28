// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Path

<<<<<<< HEAD
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.{AbstractError, Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult}
=======
>>>>>>> upstream/master
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.frontend.DefaultStates
import viper.silver.reporter.NoopReporter
<<<<<<< HEAD
import viper.silver.plugin.PluginAwareReporter

class SiliconTests extends SilSuite {
  private val siliconTestDirectories =
    Seq("consistency", "issue387")

  private val silTestDirectories =
    Seq(
    "gradual",
    "all"
        )

//  private val silTestDirectories = Seq("my-tests")

  //val testDirectories: Seq[String] = siliconTestDirectories ++ silTestDirectories
  val testDirectories: Seq[String] = silTestDirectories

=======
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.Verifier

class SiliconTests extends SilSuite {
  private val siliconTestDirectories =
    Seq("consistency")

  private val silTestDirectories =
    Seq("all",
        "quantifiedpermissions", "quantifiedpredicates", "quantifiedcombinations",
        "wands", "termination", "refute",
        "examples")

  val testDirectories: Seq[String] = siliconTestDirectories ++ silTestDirectories
>>>>>>> upstream/master

  override def frontend(verifier: Verifier, files: Seq[Path]): SiliconFrontend = {
    require(files.length == 1, "tests should consist of exactly one file")

<<<<<<< HEAD
    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    // SymbExLogger.reset()
    // SymbExLogger.filePath = files.head
    // SymbExLogger.initUnitTestEngine()

    /* If needed, Silicon reads the filename of the program under verification from Verifier.inputFile.
    When the test suite is executed (sbt test/testOnly), Verifier.inputFile is set here. When Silicon is
    run from the command line, Verifier.inputFile is set in src/main/scala/Silicon.scala. */
    viper.silicon.verifier.Verifier.inputFile = Some(files.head)

    val fe = new SiliconFrontend(NoopReporter)//SiliconFrontendWithUnitTesting()
=======
    val fe = new SiliconFrontend(NoopReporter)
>>>>>>> upstream/master
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def annotationShouldLeadToTestCancel(ann: LocatedAnnotation): Boolean = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, issue) => issue != 34
      case _ => false
    }
  }

<<<<<<< HEAD
  val silicon = {
    val reporter = PluginAwareReporter(NoopReporter)
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    new Silicon(reporter, debugInfo)
  }

  def verifiers = List(silicon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]) = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    silicon.parseCommandLine(args :+ Silicon.dummyInputFilename)
  }
  val commandLineArguments: Seq[String] =
    Seq("--timeout", "300" /* seconds */)

}

class SiliconFrontendWithUnitTesting extends SiliconFrontend(NoopReporter) {
  /** Is overridden only to append SymbExLogging-UnitTesting-Errors to the Result. **/
  override def result: SilVerificationResult = {
    super.result
    /*
    if(_state < DefaultStates.Verification) super.result
    else{
      val symbExLogUnitTestErrors = SymbExLogger.unitTestEngine.verify()
      symbExLogUnitTestErrors match{
        case Nil => super.result
        case s1:Seq[AbstractError] => super.result match{
          case SilSuccess => SilFailure(s1)
          case SilFailure(s2) => SilFailure(s2 ++ s1)
        }
      }
    }
    */
=======
  val silicon: Silicon = {
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    new Silicon(reporter, debugInfo)
>>>>>>> upstream/master
  }

  def verifiers: Seq[Silicon] = Seq(silicon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    silicon.parseCommandLine(commandLineArguments ++ args :+ Silicon.dummyInputFilename)
  }

  val commandLineArguments: Seq[String] =
    Seq("--timeout", "600" /* seconds */)
}
