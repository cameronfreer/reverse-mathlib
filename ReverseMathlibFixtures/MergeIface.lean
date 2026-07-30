/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.IfaceA
import ReverseMathlibFixtures.IfaceB

/-! # Fixture merge: two variants independently claiming one Lean interface. -/

/--
error: concept catalog: conflicted state:
  Lean interface 'FixtureProp' is owned by two statement variants ('fixIfA' and 'fixIfB')
-/
#guard_msgs in
#rm_concepts
