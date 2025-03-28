// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import java.io.File
import java.net.URL
import scala.reflect.ClassTag
import fastparse.all
import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.PreambleContributor
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.DefaultSymbolConverter
import viper.silicon.state.terms._

abstract class BuiltinDomainsContributor extends PreambleContributor[Sort, DomainFun, Term] {
  type BuiltinDomainType <: ast.GenericType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType]

  def defaultSourceResource: String
  def userProvidedSourceFilepath: Option[String]

  lazy val sourceUrl: URL = {
    userProvidedSourceFilepath
      .map(filepath => new File(filepath).toURI.toURL)
      .getOrElse(getClass.getResource(defaultSourceResource))
  }

  def sourceDomainName: String
  def domainTranslator: DomainsTranslator[Term]
  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort

  protected lazy val symbolConverter: BuiltinDomainAwareSymbolConverter =
    new BuiltinDomainAwareSymbolConverter(sourceDomainName, targetSortFactory)

  private var collectedSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty
  private var collectedFunctions = InsertionOrderedSet[DomainFun]()
  private var collectedAxioms = InsertionOrderedSet[Term]()

  /* Lifetime */

  def reset() {
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctions = InsertionOrderedSet.empty
    collectedAxioms = InsertionOrderedSet.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    val builtinDomainTypeInstances = computeGroundTypeInstances(program)
    val sourceProgram = utils.loadProgramFromUrl(sourceUrl)
    val sourceDomain = transformSourceDomain(sourceProgram.findDomain(sourceDomainName))

    val sourceDomainTypeInstances =
      builtinDomainTypeInstances map (builtinTypeInstance =>
        ast.DomainType(sourceDomain, sourceDomain.typVars.zip(builtinTypeInstance.typeArguments).toMap))

    /* For each necessary domain type, instantiate the corresponding domain */
    val sourceDomainInstantiations =
      sourceDomainTypeInstances map (mdt => {
        /* TODO: Copied from DomainInstances.getInstanceMembers.
         *       Cannot directly use that because it filters according to which domain instances
         *       are used in the program from which the source domain was loaded, whereas the
         *       instances should be filtered according to which are used in the program under
         *       verification.
         */
        val functions = sourceDomain.functions.map(ast.utility.DomainInstances.substitute(_, mdt.typVarsMap, sourceProgram)).distinct
        val axioms = sourceDomain.axioms.map(ast.utility.DomainInstances.substitute(_, mdt.typVarsMap, sourceProgram)).distinct

        val instance =
          sourceDomain.copy(functions = functions, axioms = axioms)(sourceDomain.pos, sourceDomain.info, sourceDomain.errT)

        transformSourceDomainInstance(instance, mdt)
      })

    collectSorts(sourceDomainTypeInstances)
    collectFunctions(sourceDomainInstantiations)
    collectAxioms(sourceDomainInstantiations)
  }

  protected def computeGroundTypeInstances(program: ast.Program): InsertionOrderedSet[BuiltinDomainType] =
    program.groundTypeInstances.collect {
      case builtinDomainTypeTag(s) => s
    }.to[InsertionOrderedSet]

  protected def transformSourceDomain(sourceDomain: ast.Domain): ast.Domain = sourceDomain

  protected def transformSourceDomainInstance(sourceDomain: ast.Domain, typ: ast.DomainType): ast.Domain = sourceDomain

  protected def collectSorts(domainTypes: Iterable[ast.DomainType]) {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    domainTypes.foreach(domainType => {
      val domainSort = symbolConverter.toSort(domainType)
      collectedSorts += domainSort
    })
  }

  protected def collectFunctions(domains: Set[ast.Domain]) {
    domains foreach (
      _.functions foreach (df =>
        collectedFunctions += symbolConverter.toFunction(df)))
  }

  protected def collectAxioms(domains: Set[ast.Domain]) {
    domains foreach (
      _.axioms foreach (ax =>
        collectedAxioms += translateAxiom(ax)))
  }

  protected def translateAxiom(ax: ast.DomainAxiom): Term = {
    /* Use builtin equality instead of the type-specific one.
     * Uses of custom equality functions, i.e. applications of the uninterpreted equality function,
     * are preserved.
     */
    domainTranslator.translateAxiom(ax, symbolConverter.toSort).transform {
      case Equals(t1, t2) => BuiltinEquals(t1, t2)
    }(recursive = _ => true)
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort/*sorts.Multiset*/] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  def symbolsAfterAnalysis: InsertionOrderedSet[DomainFun] =
    collectedFunctions

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
    collectedFunctions foreach (f => sink.declare(FunctionDecl(f)))
  }

  def axiomsAfterAnalysis: Iterable[Term] = collectedAxioms

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    collectedAxioms foreach (ax => sink.assume(ax))
  }

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}

class BuiltinDomainAwareSymbolConverter(sourceDomainName: String,
                                        targetSortFactory: Iterable[Sort] => Sort)
    extends DefaultSymbolConverter {

  override def toSort(typ: ast.Type): Sort = typ match {
    case dt: ast.DomainType if dt.domainName == sourceDomainName =>
      targetSortFactory(dt.typVarsMap.values map toSort)
    case other =>
      super.toSort(other)
  }
}

private object utils {
  def loadProgramFromResource(resource: String): ast.Program = {
    loadProgramFromUrl(getClass.getResource(resource))
  }

  // TODO: Check that Silver's parser doesn't already provide suitable functionality.
  def loadProgramFromUrl(url: URL): ast.Program = {
    assert(url != null, s"Unexpectedly found sourceUrl == null")

    val fromPath = viper.silver.utility.Paths.pathFromResource(url)
    val source = scala.io.Source.fromURL(url)

    val content =
      try {
        source.mkString
      } catch {
        case e@(_: RuntimeException | _: java.io.IOException) =>
          sys.error(s"Could not read from $url. Exception: $e")
      } finally {
        source.close()
      }

    viper.silver.parser.FastParser.parse(content, fromPath) match {
      case fastparse.core.Parsed.Success(parsedProgram: viper.silver.parser.PProgram, _) =>
        assert(parsedProgram.errors.isEmpty, s"Unexpected parsing errors: ${parsedProgram.errors}")

        val resolver = viper.silver.parser.Resolver(parsedProgram)
        val resolved = resolver.run.get
        val translator = viper.silver.parser.Translator(resolved)
        val program = translator.translate.get

        program

      case fastparse.core.Parsed.Failure(msg, index, extra) =>
        val (line, col) = ast.LineCol(extra.input.asInstanceOf[all.ParserInput], index)
        sys.error(s"Failure: $msg, at ${viper.silver.parser.FilePosition(fromPath, line, col)}")
    }
  }
}
