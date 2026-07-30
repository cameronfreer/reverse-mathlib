/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.SchemaA
import ReverseMathlibFixtures.SchemaB

/-! # Fixture merge: one layer id registered by two siblings with different interface
schemas. Each sibling compiles cleanly; only a module importing both observes the duplicate —
so mismatched schema expectations can never coexist in a clean catalog. -/

/--
error: concept catalog: conflicted state:
  duplicate semantic layer 'fixdupschemalayer'
-/
#guard_msgs in
#rm_concepts
