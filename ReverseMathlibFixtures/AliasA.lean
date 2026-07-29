/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture A: registers `fixzoo:"X"` as an exact alias of its own concept.
Compiles cleanly in isolation — the collision only exists in a module importing both siblings. -/

rm_concept fixConceptA where
  description := "fixture concept registered by module AliasA"

rm_external_ref fixzoo "X" exactAlias concept fixConceptA
