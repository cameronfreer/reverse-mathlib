/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.BigraphToSystem

/-!
# The 2-regular matchingω direction theorems (issue #42)

The forward direction `EFILCω → 2-regular matchingω`: compile the bigraph to an
internal inverse system (`bigraphToSystem`), take a section, decode it
(`sectionMatchingFunction`). Injectivity and right-saturation both come from the
mate-table frontier consistency at a sufficiently high level, transported down by
the iterated section coherence — exactly the source's argument that a path
through the mate-table tree is a perfect matching.

Deliberately an **ordinary unregistered theorem**: the equivalence is registered
only when both directions, the exact semantic certificate, and the goldens land
atomically (final slice). The reversal (through the bridge-local disjoint-range
separation interface) arrives in the later slices.
-/

namespace ReverseMathlib.Omega

/-- The structure of a section value: at level `m` it is a consistent mate table
for the level-`m` transcripts, and each entry's components are enumerated
neighbors of its index. -/
private theorem section_value_shape {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {G : InternalTwoRegularBigraph Ω} {s : InternalFunction Ω}
    (hs : (bigraphToSystem G h).IsSection s) {m cm : ℕ} (hcm : s.MapsTo m cm) :
    cm ∈ mateLevelList G.leftEnum.eval G.rightEnum.eval m := by
  have hfib : (bigraphToSystem G h).fibers.MapsTo m
      (seqCode (mateLevelList G.leftEnum.eval G.rightEnum.eval m)) := ⟨m, rfl⟩
  have hmem := hs.1 m _ cm hfib hcm
  rwa [decodeSeq_seqCode] at hmem

/-- Entry components of a section value are enumerated neighbors, and the whole
table is frontier-consistent. -/
private theorem section_value_entries {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {G : InternalTwoRegularBigraph Ω} {s : InternalFunction Ω}
    (hs : (bigraphToSystem G h).IsSection s) {m cm : ℕ} (hcm : s.MapsTo m cm) :
    MateConsistent (decodeSeq cm) ∧ ∀ k, k < m →
      ((decodeSeq cm).getD k 0).unpair.1 ∈ decodeSeq (G.leftEnum.eval k) ∧
      ((decodeSeq cm).getD k 0).unpair.2 ∈ decodeSeq (G.rightEnum.eval k) := by
  obtain ⟨hbad, i, hi, rfl⟩ := mem_mateLevelList_iff.mp (section_value_shape hs hcm)
  rw [decodeSeq_seqCode]
  refine ⟨mateBadCount_eq_zero_iff.mp hbad, fun k hk => ?_⟩
  rw [mateTable_getD hk, valueTable_getD hk, valueTable_getD hk, mateEntry,
    Nat.unpair_pair]
  dsimp only
  have hd := mateDigits_lt (i := i) hk
  have hll : (decodeSeq (G.leftEnum.eval k)).length = 2 :=
    G.left_two_regular k _ (G.leftEnum.pair_eval_mem k)
  have hrl : (decodeSeq (G.rightEnum.eval k)).length = 2 :=
    G.right_two_regular k _ (G.rightEnum.pair_eval_mem k)
  constructor
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by rw [hll]; omega), Option.getD_some]
    exact List.getElem_mem _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by rw [hrl]; exact Nat.div_lt_of_lt_mul (by omega)), Option.getD_some]
    exact List.getElem_mem _

/-- Entries are stable across levels: entry `k` of the level-`m` value agrees with
entry `k` of any higher-level value. -/
private theorem section_value_stable {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {G : InternalTwoRegularBigraph Ω} {s : InternalFunction Ω}
    (hs : (bigraphToSystem G h).IsSection s) {m m' cm cm' k : ℕ}
    (hk : k < m) (hmm : m ≤ m') (hcm : s.MapsTo m cm) (hcm' : s.MapsTo m' cm') :
    (decodeSeq cm).getD k 0 = (decodeSeq cm').getD k 0 := by
  have htake := mate_section_value_take hs hmm hcm' hcm
  rw [htake, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

/-- **`EFILCω → 2-regular matchingω`** over a Turing ideal: compile the bigraph
to an internal inverse system, take a section, and decode it to an internal
graph-coded perfect matching. Edge-respect reads the enumerated neighbor through
`mem_iff`; injectivity and right-saturation both come from frontier consistency
at a level beyond every vertex involved, transported down by the iterated section
coherence. -/
theorem twoRegularPerfectMatchingAt_of_efilcAt {Ω : OmegaPart}
    (h : IsTuringIdeal Ω) (hefilc : EFILCAt Ω) : TwoRegularPerfectMatchingAt Ω := by
  intro G
  obtain ⟨s, hs⟩ := hefilc (bigraphToSystem G h)
  have hlen : ∀ {m cm}, s.MapsTo m cm → (decodeSeq cm).length = m := by
    intro m cm hcm
    obtain ⟨-, i, -, rfl⟩ := mem_mateLevelList_iff.mp (section_value_shape hs hcm)
    rw [decodeSeq_seqCode, mateTable_length]
  refine ⟨sectionMatchingFunction h s, ?_, ?_, ?_⟩
  · -- edge-respecting
    intro n y hny
    obtain ⟨c, hc, hval⟩ := sectionMatchingFunction_mapsTo_iff.mp hny
    have hent := ((section_value_entries hs hc).2 n (by omega)).1
    rw [hval] at hent
    exact (G.left_mem_iff n _ y (G.leftEnum.pair_eval_mem n)).mp hent
  · -- injective
    intro n n' y hn hn'
    obtain ⟨c, hc, hval⟩ := sectionMatchingFunction_mapsTo_iff.mp hn
    obtain ⟨c', hc', hval'⟩ := sectionMatchingFunction_mapsTo_iff.mp hn'
    set m := max (max n n') y + 1 with hm
    obtain ⟨cm, hcm⟩ := s.total m
    have hcons := (section_value_entries hs hcm).1
    have hlenm := hlen hcm
    have h1 : ((decodeSeq cm).getD n 0).unpair.1 = y := by
      rw [← section_value_stable hs (by omega) (by omega) hc hcm, hval]
    have h1' : ((decodeSeq cm).getD n' 0).unpair.1 = y := by
      rw [← section_value_stable hs (by omega) (by omega) hc' hcm, hval']
    have hy1 := (hcons n (by omega) y (by omega)).mp h1
    have hy2 := (hcons n' (by omega) y (by omega)).mp h1'
    rw [hy1] at hy2
    exact hy2
  · -- right-surjective
    intro y
    obtain ⟨cy, hcy⟩ := s.total (y + 1)
    set x := ((decodeSeq cy).getD y 0).unpair.2 with hx
    set m := max x y + 2 with hm
    obtain ⟨cm, hcm⟩ := s.total m
    have hcons := (section_value_entries hs hcm).1
    have hlenm := hlen hcm
    have hxm : ((decodeSeq cm).getD y 0).unpair.2 = x := by
      rw [← section_value_stable hs (by omega) (by omega) hcy hcm]
    have h1 : ((decodeSeq cm).getD x 0).unpair.1 = y :=
      (hcons x (by omega) y (by omega)).mpr hxm
    obtain ⟨cx, hcx⟩ := s.total (x + 1)
    refine ⟨x, sectionMatchingFunction_mapsTo_iff.mpr ⟨cx, hcx, ?_⟩⟩
    rw [section_value_stable hs (by omega) (by omega) hcx hcm]
    exact h1

end ReverseMathlib.Omega
