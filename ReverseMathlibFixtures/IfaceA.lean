/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture IfaceA: variant `fixIfA` owns the Lean interface `FixtureProp`. -/

rm_statement_variant fixIfA where
  concept := fixBaseConcept
  layer := fixlayer
  interface := FixtureProp
  description := "fixture interface owner A"
