/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture VarB: independently registers statement variant `fixVar`. -/

rm_statement_variant fixVar where
  concept := fixBaseConcept
  layer := fixlayer
  description := "fixture variant registered by VarB"
