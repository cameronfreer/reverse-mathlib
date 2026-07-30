/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.VarA
import ReverseMathlibFixtures.VarB

/-! # Fixture merge: duplicate statement-variant ids across siblings. -/

/--
error: concept catalog: conflicted state:
  duplicate statement-variant id 'fixVar'
-/
#guard_msgs in
#rm_concepts
