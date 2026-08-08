/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.BoundedTreeToSystem
import ReverseMathlib.Omega.Equivalence

/-!
# The bounded-Kőnigω ⇄ WKLω equivalence (issue #39, slice 4)

The integration theorems. Each is deliberately an **ordinary unregistered theorem**: the
equivalence is registered only when the production fact, the exact semantic equivalence
certificate, and the goldens land atomically (final slice).

The three routes:

* `boundedKonigAt_of_efilcAt` — compile the bounded tree to an internal inverse system
  (`boundedTreeToSystem`), take a section, decode it (`sectionBoundedPathFunction`);
* `weakKonigAt_of_boundedKonigAt` — the **specialization**: a binary tree is an explicitly
  bounded tree for the constant bound `2` (recursive graph, so internal to every ideal);
  the bounded path's bit-`1` positions form the binary path;
* `boundedKonigAt_of_weakKonigAt` — purely compositional through the frozen
  `efilcAt_of_weakKonigAt`; no new construction.
-/

namespace ReverseMathlib.Omega

/-! ### Specialization glue: the constant bound and the bit-`1` positions

Layered like every construction: raw recursive graph, packaging by ideal closure. -/

/-- Layer 1 (raw): the graph of the constant function with value `b`. -/
def constBoundGraph (b : ℕ) : Set ℕ := {p | ∃ i, p = Nat.pair i b}

/-- Membership in the constant graph is an equation on the unpaired value. -/
theorem mem_constBoundGraph_iff {b p : ℕ} : p ∈ constBoundGraph b ↔ p.unpair.2 = b := by
  constructor
  · rintro ⟨i, rfl⟩
    simp [Nat.unpair_pair]
  · intro hb
    exact ⟨p.unpair.1, by rw [← hb, Nat.pair_unpair]⟩

/-- The constant graph is recursive. -/
theorem recursiveSet_constBoundGraph (b : ℕ) : RecursiveSet (constBoundGraph b) := by
  have hchar : Primrec fun p : ℕ => if p.unpair.2 = b then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const b))
      (.const 1) (.const 0)
  have hp : Nat.Partrec fun p => Part.some (if p.unpair.2 = b then 1 else 0) :=
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hchar)).of_eq fun _ => rfl
  refine hp.of_eq fun p => ?_
  simp only [charFn]
  by_cases hmem : p ∈ constBoundGraph b
  · rw [if_pos (mem_constBoundGraph_iff.mp hmem), if_pos hmem]
  · rw [if_neg (fun hc => hmem (mem_constBoundGraph_iff.mpr hc)), if_neg hmem]

/-- The constant bound as an internal graph-coded function — internal to **every** Turing
ideal, since its graph is recursive. -/
def constBoundFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω) (b : ℕ) :
    InternalFunction Ω where
  graph := ⟨constBoundGraph b, h.mem_of_recursive (recursiveSet_constBoundGraph b)⟩
  total := fun i => ⟨b, ⟨i, rfl⟩⟩
  singleValued := fun i y y' hy hy' => by
    have h1 := mem_constBoundGraph_iff.mp hy
    have h2 := mem_constBoundGraph_iff.mp hy'
    simp only [Nat.unpair_pair] at h1 h2
    rw [h1, h2]

/-- Layer 1 (raw): the bit-`1` positions of a graph-coded path function. Mentions **only**
the path graph. -/
def pathOneSet {Ω : OmegaPart} (p : InternalFunction Ω) : Set ℕ := {i | p.MapsTo i 1}

/-- The bit-`1` positions are Turing-reducible to the path graph — a single oracle query
at `Nat.pair i 1`. -/
theorem pathOneSet_le_graph {Ω : OmegaPart} (p : InternalFunction Ω) :
    pathOneSet p ≤ᵀ p.graph.1 := by
  have hpairone : Nat.Partrec fun i => Part.some (Nat.pair i 1) := by
    have : Primrec fun i : ℕ => Nat.pair i 1 :=
      Primrec₂.natPair.comp Primrec.id (.const 1)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have horacle := recursiveIn_comp_partrec
    (Nat.RecursiveIn.oracle (O := {charFn p.graph.1}) _ rfl) hpairone
  refine horacle.of_eq fun i => ?_
  simp only [charFn]
  by_cases hm : p.MapsTo i 1
  · rw [if_pos (show Nat.pair i 1 ∈ p.graph.1 from hm),
      if_pos (show i ∈ pathOneSet p from hm)]
  · rw [if_neg (show Nat.pair i 1 ∉ p.graph.1 from hm),
      if_neg (show i ∉ pathOneSet p from hm)]

/-! ### First direction: `EFILCω → bounded-Kőnigω` -/

/-- **`EFILCω → bounded-Kőnigω`** over a Turing ideal: compile the bounded tree to an
internal inverse system (`boundedTreeToSystem`), take a section, and decode it to an
internal graph-coded path (`sectionBoundedPathFunction`). Path correctness runs the four
steps: select a level-`n` section value proof-locally; fiber membership yields a genuine
length-`n` tree node; `bounded_section_value_take` relates it to every level-`i + 1`
value; the relational path statement converts the entry. -/
theorem boundedKonigAt_of_efilcAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hefilc : EFILCAt Ω) : BoundedKonigAt Ω := by
  intro T hlev
  obtain ⟨s, hs⟩ := hefilc (boundedTreeToSystem h T hlev)
  refine ⟨sectionBoundedPathFunction h s, fun n => ?_⟩
  -- Step 1: select the level-`n` section value — proof-local.
  obtain ⟨cn, hcn⟩ := s.total n
  -- Step 2: fiber membership makes it a genuine length-`n` tree node.
  have hfib : (boundedTreeToSystem h T hlev).fibers.MapsTo n
      (seqCode (boundedLevelList T.tree.1 T.bound.eval n)) := ⟨n, rfl⟩
  have hmem := hs.1 n _ cn hfib hcn
  rw [decodeSeq_seqCode] at hmem
  obtain ⟨hcnT, idx, hidx, hcneq⟩ := mem_boundedLevelList_iff.mp hmem
  have hlen : (decodeSeq cn).length = n := by
    rw [hcneq, decodeSeq_seqCode, digitListOfIndex_length]
    simp [radixList]
  refine ⟨cn, hcnT, hlen, fun i hi v hv => ?_⟩
  -- Step 3: iterated coherence relates the level-`n` node to the level-`i + 1` value.
  obtain ⟨ci, hci, hval⟩ := sectionBoundedPathFunction_mapsTo_iff.mp hv
  have htake : ci = seqCode ((decodeSeq cn).take (i + 1)) :=
    bounded_section_value_take (h := h) (T := T) (hlev := hlev) hs (by omega) hcn hci
  -- Step 4: the relational path statement converts the entry at position `i`.
  have hent : (decodeSeq ci).getD i 0 = (decodeSeq cn).getD i 0 := by
    rw [htake, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  rw [← hval, hent]

/-! ### Second direction: `bounded-Kőnigω → WKLω` — the specialization -/

/-- **`bounded-Kőnigω → WKLω`** over a Turing ideal: a binary tree is an explicitly
bounded tree for the constant bound `2` — the bound certificate comes from
binary-valuedness, the packaging from recursiveness of the constant graph. The bounded
path's bit-`1` positions (`pathOneSet`, internal by a single-query reduction) form the
binary path. -/
theorem weakKonigAt_of_boundedKonigAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hbkl : BoundedKonigAt Ω) : WeakKonigAt Ω := by
  intro T htree hlev
  obtain ⟨p, hp⟩ := hbkl
    { tree := T
      bound := constBoundFunction h 2
      entry_lt_bound := fun c hc i b hi hb => by
        have hb2 : b = 2 := by
          have := mem_constBoundGraph_iff.mp hb
          simpa [Nat.unpair_pair] using this
        subst hb2
        have hmem' : (decodeSeq c).getD i 0 ∈ decodeSeq c := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
          exact List.getElem_mem hi
        have := htree.1 c hc _ hmem'
        omega
      prefix_closed := htree.2 } hlev
  refine ⟨⟨pathOneSet p, h.mem_of_reducible p.graph.2 (pathOneSet_le_graph p)⟩,
    fun n => ?_⟩
  obtain ⟨c, hcT, hlen, hagree⟩ := hp n
  refine ⟨c, hcT, hlen, fun i hi => ?_⟩
  obtain ⟨v, hv⟩ := p.total i
  have hev : (decodeSeq c).getD i 0 = v := hagree i hi v hv
  constructor
  · intro hone
    have hv1 : v = 1 := by omega
    change p.MapsTo i 1
    rw [← hv1]
    exact hv
  · intro hmem
    have h1v := p.singleValued i 1 v hmem hv
    omega

/-! ### The composed converse: `WKLω → bounded-Kőnigω`

Purely compositional through the frozen `efilcAt_of_weakKonigAt` — no new construction,
and the route is visible in the proof term: WKLω compiles systems to binary trees, and
bounded trees compile to systems. -/

/-- **`WKLω → bounded-Kőnigω`** over a Turing ideal, through EFILCω. -/
theorem boundedKonigAt_of_weakKonigAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hwkl : WeakKonigAt Ω) : BoundedKonigAt Ω :=
  boundedKonigAt_of_efilcAt h (efilcAt_of_weakKonigAt h hwkl)

end ReverseMathlib.Omega
