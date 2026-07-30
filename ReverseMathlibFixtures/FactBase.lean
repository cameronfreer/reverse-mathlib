/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture FactBase: shared vocabulary and endpoints for cross-module fact collisions. -/

rm_base_theory fixFactBase "fixture base theory for fact collision tests"

rm_statement_variant fixFactVarX where
  concept := fixBaseConcept
  layer := fixlayer
  description := "fixture literature-only variant X"

rm_statement_variant fixFactVarY where
  concept := fixBaseConcept
  layer := fixlayer
  description := "fixture literature-only variant Y"
