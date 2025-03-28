// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silicon.{Map, toMap}
<<<<<<< HEAD
import viper.silicon.state.terms.{Term, sorts}
import viper.silver.ast.AbstractLocalVar

trait Store {
  def values: Map[ast.AbstractLocalVar, Term]
  def apply(key: ast.AbstractLocalVar): Term
  def get(key: ast.AbstractLocalVar): Option[Term]
  def getKeyForValue(termVariable: terms.Term, lenient: Boolean = false): Option[ast.AbstractLocalVar]
  def +(kv: (ast.AbstractLocalVar, Term)): Store
=======
import viper.silicon.state.terms.Term
import viper.silver.ast.AbstractLocalVar

trait Store {
  def values: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])]
  def termValues: Map[ast.AbstractLocalVar, Term]
  def expValues: Map[ast.AbstractLocalVar, Option[ast.Exp]]
  def apply(key: ast.AbstractLocalVar): Term
  def get(key: ast.AbstractLocalVar): Option[Term]
  def getExp(key: ast.AbstractLocalVar): Option[ast.Exp]
  def +(kv: (ast.AbstractLocalVar, (Term, Option[ast.Exp]))): Store
>>>>>>> upstream/master
  def +(other: Store): Store
}

trait StoreFactory[ST <: Store] {
  def apply(): ST
<<<<<<< HEAD
  def apply(bindings: Map[ast.AbstractLocalVar, Term]): ST
  def apply(pair: (ast.AbstractLocalVar, Term)): ST
  def apply(pairs: Iterable[(ast.AbstractLocalVar, Term)]): ST
=======
  def apply(bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])]): ST
  def apply(pair: (ast.AbstractLocalVar, (Term, Option[ast.Exp]))): ST
  def apply(pairs: Iterable[(ast.AbstractLocalVar, (Term, Option[ast.Exp]))]): ST
>>>>>>> upstream/master
}

object Store extends StoreFactory[MapBackedStore] {
  def apply() = new MapBackedStore(Map.empty)
<<<<<<< HEAD
  def apply(pair: (AbstractLocalVar, Term)) = new MapBackedStore(Map(pair))
  def apply(bindings: Map[AbstractLocalVar, Term]) = new MapBackedStore(toMap(bindings))
  def apply(bindings: Iterable[(AbstractLocalVar, Term)]) = new MapBackedStore(toMap(bindings))
}

final class MapBackedStore private[state] (map: Map[ast.AbstractLocalVar, Term])
    extends Store with Immutable {

  val values = map
  def apply(key: ast.AbstractLocalVar) = map(key)
  def get(key: ast.AbstractLocalVar) = map.get(key)
  def getKeyForValue(symbolicVariable: terms.Term, lenient: Boolean = false): Option[ast.AbstractLocalVar] = {
    // TODO: clean this up!
    symbolicVariable match {
      case var1 @ terms.Var(identifier1, sort1) =>
        map.find({
          case (k, var2 @ terms.Var(identifier2, sort2)) => {
            if (lenient) {
              identifier1.toString == identifier2.toString && sort1 == sort2
            } else {
              var1 == var2
            }
          }
          case (k, term2) if term2.sort == sorts.Ref => {
            if (lenient) {
              symbolicVariable.toString == term2.toString && sort1 == term2.sort
            } else {
              var1 == term2
            }
          }
          case _ => false
        }) match {
            case None => None
            // retreives the key? i think (without having to pattern match...) maybe
            case Some(kv) => Some(kv._1)
        }
      case _ => map.find({
          case (k, var2) => {
              symbolicVariable == var2
          }
          case _ => false
        }) match {
            case None => None
            // retreives the key? i think (without having to pattern match...) maybe
            case Some(kv) => Some(kv._1)
        }

    }
  }
  def +(entry: (ast.AbstractLocalVar, Term)) = new MapBackedStore(map + entry)
=======
  def apply(pair: (AbstractLocalVar, (Term, Option[ast.Exp]))) = new MapBackedStore(Map(pair))
  def apply(bindings: Map[AbstractLocalVar, (Term, Option[ast.Exp])]) = new MapBackedStore(toMap(bindings))
  def apply(bindings: Iterable[(AbstractLocalVar, (Term, Option[ast.Exp]))]) = new MapBackedStore(toMap(bindings))
}

final class MapBackedStore private[state] (map: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])])
    extends Store {

  val values = map

  def termValues = values.map{case (localVar, pair) => localVar -> pair._1}
  def expValues = values.map{case (localVar, pair) => localVar -> pair._2}
  def apply(key: ast.AbstractLocalVar) = map(key)._1
  def get(key: ast.AbstractLocalVar) = termValues.get(key)
  def getExp(key: ast.AbstractLocalVar) = expValues.get(key) match {
    case Some(e) => e
    case None => None
  }
  def +(entry: (ast.AbstractLocalVar, (Term, Option[ast.Exp]))) = new MapBackedStore(map + entry)
>>>>>>> upstream/master
  def +(other: Store) = new MapBackedStore(map ++ other.values)
}
