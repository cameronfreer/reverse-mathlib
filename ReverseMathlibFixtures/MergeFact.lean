/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.FactA
import ReverseMathlibFixtures.FactB

/-! # Fixture merge: two siblings independently registering the same fact content.

Each compiles cleanly; a module importing both observes the duplicate — conjunction
normalization makes the permuted, conjunct-duplicated copies collide. -/

/--
error: concept catalog: conflicted state:
  duplicate fact content: 'fixFactB' repeats 'fixFactA'
-/
#guard_msgs in
#rm_facts
