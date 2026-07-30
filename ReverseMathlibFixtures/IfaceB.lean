/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture IfaceB: variant `fixIfB` independently claims the same Lean interface. -/

rm_statement_variant fixIfB where
  concept := fixBaseConcept
  layer := fixlayer
  interface := FixtureProp
  description := "fixture interface owner B"
