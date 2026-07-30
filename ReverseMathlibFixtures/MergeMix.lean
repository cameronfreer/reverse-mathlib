/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.MixA
import ReverseMathlibFixtures.MixB

/-! # Fixture merge: one exact alias targeting a concept in one module and a statement
variant in another. -/

/--
error: concept catalog: conflicted state:
  exact alias fixzoo:"Y" resolves to two different targets ('fixBaseConcept' and 'fixMixVar')
-/
#guard_msgs in
#rm_concepts
