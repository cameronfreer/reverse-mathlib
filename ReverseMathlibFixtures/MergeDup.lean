/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.DupA
import ReverseMathlibFixtures.DupB

/-! # Fixture merge: duplicate concept ids across independently developed siblings. -/

/--
error: concept catalog: conflicted state:
  duplicate concept id 'fixDup'
-/
#guard_msgs in
#rm_concepts
