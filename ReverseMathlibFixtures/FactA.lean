/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.FactBase

/-! # Fixture FactA: registers an implication fact `X+Y => X`. -/

rm_fact fixFactA implication where
  base := fixFactBase
  scope := provability
  lhs := [fixFactVarX, fixFactVarY]
  rhs := [fixFactVarX]
