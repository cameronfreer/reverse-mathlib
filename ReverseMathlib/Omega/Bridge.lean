/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.BitCoding
import ReverseMathlib.Omega.Equivalence
import ReverseMathlib.Omega.PathToSection
import ReverseMathlib.Omega.SystemToTree
import ReverseMathlib.Omega.TreeToSystem

/-!
# The WKLω ⇄ EFILCω bridge constructions (issue #22, slice 3)

This module contains no mathematics; it is the import surface for the five bridge modules.

* `ReverseMathlib.Omega.BitCoding` — the structural bit-vector enumeration.
* `ReverseMathlib.Omega.TreeToSystem` — `treeToSystem` and `sectionToPath`.
* `ReverseMathlib.Omega.SystemToTree` — `systemToTree`, the verifier, the transcripts, and
  `systemTreeSet_le_systemOracle`.
* `ReverseMathlib.Omega.PathToSection` — the decoder `pathSectionValue`, its reduction
  `pathSectionGraph_le_join`, and its correctness `pathSectionFunction_isSection`.
* `ReverseMathlib.Omega.Equivalence` — the direction theorems.

These computability lemmas are simultaneously the future first ω-transfer rule set and the
source material for the represented uniform-reduction pilot.
-/
