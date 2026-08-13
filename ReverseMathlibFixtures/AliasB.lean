/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture B: independently registers `fixzoo:"X"` as an exact alias of a different
concept. Compiles cleanly in isolation. -/

rm_concept fixConceptB where
  statement := "fixture statement for fixConceptB"
  description := "fixture concept registered by module AliasB"

rm_external_ref fixzoo "X" exactAlias concept fixConceptB
