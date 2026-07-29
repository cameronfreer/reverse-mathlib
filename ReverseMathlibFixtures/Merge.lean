/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.AliasA
import ReverseMathlibFixtures.AliasB

/-! # Fixture merge: the import-wide collision test.

`AliasA` and `AliasB` each compile cleanly; only a module importing both can observe that
`fixzoo:"X"` resolves to two different targets. Registration-time checks alone cannot catch
this — the query gate must. -/

/--
error: concept catalog: conflicted state:
  exact alias fixzoo:"X" resolves to two different targets ('fixConceptA' and 'fixConceptB')
-/
#guard_msgs in
#rm_concepts
