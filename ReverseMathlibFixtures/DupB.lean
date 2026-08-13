/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture DupB: independently registers concept `fixDup`. -/

rm_concept fixDup where
  statement := "fixture statement for fixDup"
  description := "fixture duplicate concept, registered by DupB"
