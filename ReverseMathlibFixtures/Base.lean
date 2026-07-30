/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Concepts

/-! # Fixture base: a shared namespace, imported as a diamond by the sibling fixtures. -/

rm_namespace fixzoo "fixture namespace for cross-module collision tests"

rm_semantic_layer fixlayer "fixture semantic layer"

rm_concept fixBaseConcept where
  description := "fixture parent concept for variant collision tests"

/-- A fixture Prop for interface-ownership collision tests. -/
def FixtureProp : Prop := True
