/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base
import ReverseMathlibFixtures.AliasA
import ReverseMathlibFixtures.AliasB
import ReverseMathlibFixtures.DupA
import ReverseMathlibFixtures.DupB
import ReverseMathlibFixtures.Merge
import ReverseMathlibFixtures.MergeDup
import ReverseMathlibFixtures.VarA
import ReverseMathlibFixtures.VarB
import ReverseMathlibFixtures.IfaceA
import ReverseMathlibFixtures.IfaceB
import ReverseMathlibFixtures.MixA
import ReverseMathlibFixtures.MixB
import ReverseMathlibFixtures.MergeVar
import ReverseMathlibFixtures.MergeIface
import ReverseMathlibFixtures.MergeMix
import ReverseMathlibFixtures.SchemaFix
import ReverseMathlibFixtures.SchemaA
import ReverseMathlibFixtures.SchemaB
import ReverseMathlibFixtures.MergeSchema
import ReverseMathlibFixtures.FactBase
import ReverseMathlibFixtures.FactA
import ReverseMathlibFixtures.FactB
import ReverseMathlibFixtures.MergeFact

/-!
# Collision-test fixtures

Compile-time tests of the conceptual catalog's import-wide collision handling. Never imported
by any production root — `scripts/check_sorry_boundary.py` enforces that.
-/
