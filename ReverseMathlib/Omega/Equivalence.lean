/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.PathToSection
import ReverseMathlib.Omega.TreeToSystem

/-!
# The WKLω ⇄ EFILCω equivalence (issue #22, slice 3)

The integration theorems — both directions. Each is deliberately an **ordinary
unregistered theorem**: the equivalence is registered only when the input-access records,
the production equivalence fact, the exact semantic equivalence certificate, and the
goldens land atomically (stage 5).
-/

namespace ReverseMathlib.Omega

/-! ### First direction: `EFILCω → WKLω`

The integration of the completed `treeToSystem` / `sectionToPath` route. Deliberately an
**ordinary unregistered theorem**: it is registered only when both directions and the exact
semantic equivalence certificate land atomically (stage 5). Selection of the level-`n`
section value happens purely inside this proof; the constructed path is
`sectionPathInternal`, whose definition and reducibility mention only the section graph. -/

/-- **`EFILCω → WKLω`** over a Turing ideal: compile the tree to an internal inverse system
(`treeToSystem`), take a section, and decode it to an internal path (`sectionPathInternal`).
Path correctness runs the four steps: select a level-`n` section value proof-locally; fiber
membership yields a genuine length-`n` tree node; `section_value_take` relates it to every
level-`i + 1` value; the relational path statement converts the bit. -/
theorem weakKonigAt_of_efilcAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hefilc : EFILCAt Ω) : WeakKonigAt Ω := by
  intro T htree hlev
  obtain ⟨s, hs⟩ := hefilc (treeToSystem h T htree hlev)
  refine ⟨sectionPathInternal h s, fun n => ?_⟩
  -- Step 1: select the level-`n` section value — proof-local.
  obtain ⟨cn, hcn⟩ := s.total n
  -- Step 2: fiber membership makes it a genuine length-`n` tree node.
  have hfib : (treeToSystem h T htree hlev).fibers.MapsTo n
      (seqCode (treeLevelList T.1 n)) := ⟨n, rfl⟩
  have hmem := hs.1 n _ cn hfib hcn
  rw [decodeSeq_seqCode] at hmem
  obtain ⟨hcnT, idx, hidx, hcneq⟩ := mem_treeLevelList_iff.mp hmem
  have hlen : (decodeSeq cn).length = n := by
    rw [hcneq, decodeSeq_seqCode, bitListOfIndex_length]
  refine ⟨cn, hcnT, hlen, fun i hi => ?_⟩
  -- Step 3: iterated coherence relates the level-`n` node to the level-`i + 1` value.
  obtain ⟨ci, hci⟩ := s.total (i + 1)
  have htake : ci = seqCode ((decodeSeq cn).take (i + 1)) :=
    section_value_take (h := h) (T := T) (htree := htree) (hlev := hlev) hs
      (by omega) hcn hci
  -- Step 4: the relational path statement converts the bit at position `i`.
  have hbit : (decodeSeq ci).getD i 0 = (decodeSeq cn).getD i 0 := by
    rw [htake, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  constructor
  · intro hone
    exact ⟨ci, hci, by rw [hbit]; exact hone⟩
  · rintro ⟨c', hc', hone⟩
    rw [s.singleValued _ c' ci hc' hci, hbit] at hone
    exact hone

/-! ### Second direction: `WKLω → EFILCω`

The integration of the completed `systemToTree` / `pathToSection` route, purely
compositional: the system oracle is internal (join closure), so the compiled tree is
internal (`systemTreeSet_le_systemOracle` + downward closure); WKLω supplies an internal
path; the decoder packages it as an internal section (`pathSectionFunction`), correct by
`pathSectionFunction_isSection`. -/

/-- **`WKLω → EFILCω`** over a Turing ideal: compile the system to an internal binary tree
(`systemTreeSet`, internal by `systemTreeSet_le_systemOracle`), take a path, and decode it
to an internal section (`pathSectionFunction`). -/
theorem efilcAt_of_weakKonigAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hwkl : WeakKonigAt Ω) : EFILCAt Ω := by
  intro F
  have hT : systemTreeSet F ∈ Ω :=
    h.mem_of_reducible (h.join F.fibers.graph.2 F.bonding.graph.2)
      (systemTreeSet_le_systemOracle F)
  obtain ⟨P, hP⟩ := hwkl ⟨systemTreeSet F, hT⟩ (isBinaryTreeCode_systemTreeSet F)
    (hasNodeAtEveryLevel_systemTreeSet F)
  exact ⟨pathSectionFunction h F.fibers P, pathSectionFunction_isSection h F hP⟩

end ReverseMathlib.Omega
