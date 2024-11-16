// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class LoopInRecord(poz: ast.Position, s: State, p: PathConditionStack) extends DataRecord {
  // taking the position of the first invariant is not very elegant
  // but it works for now
  val value: ast.Node = null
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null
  val pos: ast.Position = poz

  override val toTypeString: String = "loop in"
}
