/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture MixB: exact alias `fixzoo:"Y"` independently targets a *statement variant*. -/

rm_statement_variant fixMixVar where
  concept := fixBaseConcept
  layer := fixlayer
  description := "fixture variant for mixed-target alias collision"

rm_external_ref fixzoo "Y" exactAlias statement fixMixVar
