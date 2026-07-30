/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.FactBase

/-! # Fixture FactB: the same fact content as FactA under a fresh id, permuted and with a
duplicated conjunct — identical after normalization. -/

rm_fact fixFactB implication where
  base := fixFactBase
  scope := provability
  lhs := [fixFactVarY, fixFactVarX, fixFactVarX]
  rhs := [fixFactVarX]
