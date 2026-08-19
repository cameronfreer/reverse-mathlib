/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.MatchingLocallyFinite
import ReverseMathlib.Omega.KonigFinitelyBranching
import ReverseMathlib.Omega.FiniteMatching

/-!
# The forward route: locally finite perfect matching from finitely-branching Kőnig
(issue #51)

Hirst's forward construction (thesis Theorem 3.1, i) → ii)): the partial-solution
tree of the marriage problem. A node of length `n` codes `n` pairs — entry `m` is
`Nat.pair (σ₁ m) (σ₂ m)`, the wife of the `m`-th boy and the husband of the `m`-th
girl — subject to the three source clauses: prospective spouses are acquainted (two
edge queries per position), and the coherence clause `σ₁ j = k ↔ σ₂ k = j`
simultaneously prohibits polygamy and insures that both spouses witness their
marriage (a pure condition on the code).

* Internality (`solutionTree_le_graph`): membership is a finite oracle transcript —
  two edge bits per position — plus a pure verifier for the coherence grid; the tree
  is one reduction below the bare edge set.
* Finite branching (`solutionTree_levelwise_bounded`): the two local-finiteness
  **properties** bound the last entry — each source clause pins one component of the
  pair, no enumerator or supplied bound anywhere.
* Infinitude (`solutionTree_hasNodeAtEveryLevel`): the finite stage. The truncation
  of the edge set below the local-finiteness bounds is a finite bipartite graph;
  the cardinality-form H_sym hypothesis transfers to Hall's condition on both
  distinguished sides, and the finite symmetric-Hall covering lemma
  (`exists_matching_covering`) provides a matching covering `{0, …, n − 1}` on both
  sides, which reads back as the level-`n` node.
* The path decoder (`pathMatchFunction`): the wife assigned to boy `a` is the first
  component of the path's entry at `a` — one unique-graph lookup per query
  (`InternalFunction.eval_recursiveIn_graph`), then pure unpairing. Coherence along
  the path yields injectivity and surjectivity; adjacency yields edge-respect.

No jump, no reversal machinery: the route reaches `FinitelyBranchingKonigAt` as a
hypothesis and the finite covering lemma, and the gates in `scripts/MetaSmoke.lean`
pin the exclusions.
-/

namespace ReverseMathlib.Omega

variable {Ω : OmegaPart}

/-! ### The partial-solution tree -/

/-- Membership of a node in the partial-solution tree over the edge set `E`: entry
`m` codes the pair `Nat.pair (σ₁ m) (σ₂ m)` — the wife of the `m`-th boy and the
husband of the `m`-th girl. The first two clauses insure that prospective spouses
are acquainted; the coherence clause simultaneously prohibits polygamy and insures
that both spouses witness their marriage (Hirst thesis p. 18, clauses 1–3). -/
def SolutionNodeOk (E : Set ℕ) (c : ℕ) : Prop :=
  (∀ m < (decodeSeq c).length,
    Nat.pair m ((decodeSeq c).getD m 0).unpair.1 ∈ E ∧
    Nat.pair ((decodeSeq c).getD m 0).unpair.2 m ∈ E) ∧
  ∀ j < (decodeSeq c).length, ∀ k < (decodeSeq c).length,
    (((decodeSeq c).getD j 0).unpair.1 = k ↔ ((decodeSeq c).getD k 0).unpair.2 = j)

/-- The partial-solution tree of a marriage problem, as a set of sequence codes. -/
def solutionTreeSet (G : InternalLocallyFiniteBigraph Ω) : Set ℕ :=
  {c | SolutionNodeOk G.edges.1 c}

/-- Reading a position of a truncated node (shared arithmetic of the closure and
level-bound proofs). -/
private theorem getD_seqCode_take {c k i : ℕ} (hi : i < k) :
    (decodeSeq (seqCode ((decodeSeq c).take k))).getD i 0 = (decodeSeq c).getD i 0 := by
  rw [decodeSeq_seqCode, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi,
    ← List.getD_eq_getElem?_getD]

theorem solutionTree_prefix_closed (G : InternalLocallyFiniteBigraph Ω) :
    ∀ c ∈ solutionTreeSet G, ∀ k,
      seqCode ((decodeSeq c).take k) ∈ solutionTreeSet G := by
  intro c hc k
  obtain ⟨hadj, hcoh⟩ := hc
  have hlen : (decodeSeq (seqCode ((decodeSeq c).take k))).length =
      min k (decodeSeq c).length := by
    rw [decodeSeq_seqCode, List.length_take]
  constructor
  · intro m hm
    rw [hlen] at hm
    rw [getD_seqCode_take (by omega)]
    exact hadj m (by omega)
  · intro j hj k' hk'
    rw [hlen] at hj hk'
    rw [getD_seqCode_take (by omega), getD_seqCode_take (by omega)]
    exact hcoh j (by omega) k' (by omega)

/-- **The local-finiteness properties establish levelwise boundedness** in the source
shape: each acquaintance clause pins one component of the last entry below the
corresponding person's bound. -/
theorem solutionTree_levelwise_bounded (G : InternalLocallyFiniteBigraph Ω) (n : ℕ) :
    ∃ k, ∀ c ∈ solutionTreeSet G, (decodeSeq c).length = n + 1 →
      (decodeSeq c).getD n 0 < k := by
  obtain ⟨k₁, hk₁⟩ := G.left_locally_finite n
  obtain ⟨k₂, hk₂⟩ := G.right_locally_finite n
  refine ⟨Nat.pair k₁ k₂, fun c hc hlen => ?_⟩
  obtain ⟨h1, h2⟩ := hc.1 n (by omega)
  have hu₁ : ((decodeSeq c).getD n 0).unpair.1 < k₁ := hk₁ _ h1
  have hu₂ : ((decodeSeq c).getD n 0).unpair.2 < k₂ := hk₂ _ h2
  calc (decodeSeq c).getD n 0
      = Nat.pair ((decodeSeq c).getD n 0).unpair.1 ((decodeSeq c).getD n 0).unpair.2 :=
        (Nat.pair_unpair _).symm
    _ < Nat.pair ((decodeSeq c).getD n 0).unpair.1 k₂ := Nat.pair_lt_pair_right _ hu₂
    _ ≤ Nat.pair k₁ k₂ := le_of_lt (Nat.pair_lt_pair_left _ hu₁)

/-! ### The finite stage: level-`n` nodes from the covering lemma -/

/-- Reading a function's values off positions of its own range-indexed table. -/
private theorem map_range_getD {α : Type*} (f : ℕ → α) {w v : ℕ} (hv : v < w)
    (d : α) : ((List.range w).map f).getD v d = f v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
  rfl

open Finset in
/-- **The finite stage establishes infinitude**: truncate the edge set below the
local-finiteness bounds, transfer the cardinality-form H_sym to Hall's condition on
both distinguished sides, and read the finite covering matching back as the
level-`n` node. -/
theorem solutionTree_hasNodeAtEveryLevel (G : InternalLocallyFiniteBigraph Ω)
    (hH : G.SatisfiesSymmetricHall) : HasNodeAtEveryLevel (solutionTreeSet G) := by
  classical
  intro n
  -- per-person neighbor bounds and the finite truncation of the edge set
  choose kL hkL using G.left_locally_finite
  choose kR hkR using G.right_locally_finite
  set KL := (Finset.range n).sup kL with hKL
  set KR := (Finset.range n).sup kR with hKR
  set En : Finset (ℕ × ℕ) :=
    ((Finset.range n ×ˢ Finset.range KL).filter fun p => Nat.pair p.1 p.2 ∈ G.edges.1) ∪
      ((Finset.range KR ×ˢ Finset.range n).filter fun p =>
        Nat.pair p.1 p.2 ∈ G.edges.1) with hEn
  have hEnE : ∀ p ∈ En, Nat.pair p.1 p.2 ∈ G.edges.1 := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).2
  -- Hall's condition on the boys' side of the truncation
  have hallA : ∀ S ⊆ Finset.range n, S.card ≤ (S.biUnion (rightNbrs En)).card := by
    intro S hS
    obtain ⟨w, hwnd, hwlen, hwadj⟩ := hH.1 S.toList S.nodup_toList
    have hsub : w.toFinset ⊆ S.biUnion (rightNbrs En) := by
      intro b hb
      obtain ⟨a, haS, hab⟩ := hwadj b (List.mem_toFinset.mp hb)
      have haS' : a ∈ S := Finset.mem_toList.mp haS
      have han : a < n := Finset.mem_range.mp (hS haS')
      have hbK : b < KL := lt_of_lt_of_le (hkL a b hab)
        (Finset.le_sup (Finset.mem_range.mpr han))
      refine Finset.mem_biUnion.mpr ⟨a, haS', mem_rightNbrs.mpr ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr han, Finset.mem_range.mpr hbK⟩, hab⟩)
    calc S.card = S.toList.length := (Finset.length_toList S).symm
      _ ≤ w.length := hwlen
      _ = w.toFinset.card := (List.toFinset_card_of_nodup hwnd).symm
      _ ≤ _ := Finset.card_le_card hsub
  -- Hall's condition on the girls' side of the truncation
  have hallB : ∀ S ⊆ Finset.range n, S.card ≤ (S.biUnion (leftNbrs En)).card := by
    intro S hS
    obtain ⟨w, hwnd, hwlen, hwadj⟩ := hH.2 S.toList S.nodup_toList
    have hsub : w.toFinset ⊆ S.biUnion (leftNbrs En) := by
      intro a ha
      obtain ⟨b, hbS, hab⟩ := hwadj a (List.mem_toFinset.mp ha)
      have hbS' : b ∈ S := Finset.mem_toList.mp hbS
      have hbn : b < n := Finset.mem_range.mp (hS hbS')
      have haK : a < KR := lt_of_lt_of_le (hkR b a hab)
        (Finset.le_sup (Finset.mem_range.mpr hbn))
      refine Finset.mem_biUnion.mpr ⟨b, hbS', mem_leftNbrs.mpr ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr haK, Finset.mem_range.mpr hbn⟩, hab⟩)
    calc S.card = S.toList.length := (Finset.length_toList S).symm
      _ ≤ w.length := hwlen
      _ = w.toFinset.card := (List.toFinset_card_of_nodup hwnd).symm
      _ ≤ _ := Finset.card_le_card hsub
  -- the finite symmetric-Hall covering lemma
  obtain ⟨M, hME, hMmatch, hMcovA, hMcovB⟩ :=
    exists_matching_covering En (Finset.range n) (Finset.range n) hallA hallB
  -- the covering matching's partner assignments
  have hσ₁ex : ∀ m, m < n → ∃ b, (m, b) ∈ M :=
    fun m hm => hMcovA m (Finset.mem_range.mpr hm)
  have hσ₂ex : ∀ m, m < n → ∃ a, (a, m) ∈ M :=
    fun m hm => hMcovB m (Finset.mem_range.mpr hm)
  set σ₁ : ℕ → ℕ := fun m => if h : m < n then (hσ₁ex m h).choose else 0 with hσ₁
  set σ₂ : ℕ → ℕ := fun m => if h : m < n then (hσ₂ex m h).choose else 0 with hσ₂
  have hσ₁mem : ∀ m, m < n → (m, σ₁ m) ∈ M := fun m hm => by
    rw [hσ₁]
    simp only [dif_pos hm]
    exact (hσ₁ex m hm).choose_spec
  have hσ₂mem : ∀ m, m < n → (σ₂ m, m) ∈ M := fun m hm => by
    rw [hσ₂]
    simp only [dif_pos hm]
    exact (hσ₂ex m hm).choose_spec
  -- the level-`n` node
  refine ⟨seqCode ((List.range n).map fun m => Nat.pair (σ₁ m) (σ₂ m)), ⟨?_, ?_⟩, by simp⟩
  · intro m hm
    rw [decodeSeq_seqCode] at hm ⊢
    simp only [List.length_map, List.length_range] at hm
    rw [map_range_getD _ hm, Nat.unpair_pair]
    refine ⟨?_, ?_⟩
    · exact hEnE (m, σ₁ m) (hME (hσ₁mem m hm))
    · exact hEnE (σ₂ m, m) (hME (hσ₂mem m hm))
  · intro j hj k hk
    rw [decodeSeq_seqCode] at hj hk ⊢
    simp only [List.length_map, List.length_range] at hj hk
    rw [map_range_getD _ hj, map_range_getD _ hk, Nat.unpair_pair, Nat.unpair_pair]
    constructor
    · intro h1
      by_contra hne
      have hd := hMmatch (j, σ₁ j) (hσ₁mem j hj) (σ₂ k, k) (hσ₂mem k hk)
        (fun hEq => hne (congrArg Prod.fst hEq).symm)
      exact hd.2 (h1.symm ▸ rfl)
    · intro h2
      by_contra hne
      have hd := hMmatch (j, σ₁ j) (hσ₁mem j hj) (σ₂ k, k) (hσ₂mem k hk)
        (fun hEq => hne (congrArg Prod.snd hEq))
      exact hd.1 (h2.symm ▸ rfl)

/-! ### Internality of the partial-solution tree

`solutionTree_le_graph` establishes internality independently of the semantic path
proof: membership is a finite oracle transcript — two edge bits per position — and a
pure verifier that finds no violation in either bit table or in the coherence
grid. -/

/-- Membership restated on the bits a program reads: the two acquaintance clauses as
one edge query per position and side, and the coherence clause on the bounded
`(j, k)` grid under the linear coding `t = j * n + k`. -/
private theorem solutionNodeOk_iff_grid (E : Set ℕ) (c : ℕ) :
    SolutionNodeOk E c ↔
      (∀ i < (decodeSeq c).length,
        Nat.pair i ((decodeSeq c).getD i 0).unpair.1 ∈ E) ∧
      (∀ i < (decodeSeq c).length,
        Nat.pair ((decodeSeq c).getD i 0).unpair.2 i ∈ E) ∧
      ∀ t < (decodeSeq c).length * (decodeSeq c).length,
        (((decodeSeq c).getD (t / (decodeSeq c).length) 0).unpair.1 =
            t % (decodeSeq c).length ↔
          ((decodeSeq c).getD (t % (decodeSeq c).length) 0).unpair.2 =
            t / (decodeSeq c).length) := by
  constructor
  · rintro ⟨hadj, hcoh⟩
    refine ⟨fun i hi => (hadj i hi).1, fun i hi => (hadj i hi).2, fun t ht => ?_⟩
    have hn : 0 < (decodeSeq c).length := by
      by_contra hz
      simp [Nat.eq_zero_of_not_pos hz] at ht
    exact hcoh _ (Nat.div_lt_iff_lt_mul hn |>.mpr ht) _ (Nat.mod_lt _ hn)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun m hm => ⟨h1 m hm, h2 m hm⟩, fun j hj k hk => ?_⟩
    have hn : 0 < (decodeSeq c).length := by omega
    have ht : j * (decodeSeq c).length + k <
        (decodeSeq c).length * (decodeSeq c).length := by
      calc j * (decodeSeq c).length + k
          < (j + 1) * (decodeSeq c).length := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
        _ ≤ (decodeSeq c).length * (decodeSeq c).length :=
            Nat.mul_le_mul_right _ hj
    have hdiv : (j * (decodeSeq c).length + k) / (decodeSeq c).length = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk]
      omega
    have hmod : (j * (decodeSeq c).length + k) % (decodeSeq c).length = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hk
    have := h3 _ ht
    rwa [hdiv, hmod] at this

/-- **The partial-solution tree is one reduction below the bare edge set** —
internality, independent of the semantic path proof. Per node: a transcript of two
edge bits per position, then a pure three-check `findIdx` verifier (both bit tables
clean, coherence grid clean). -/
theorem solutionTree_le_graph (G : InternalLocallyFiniteBigraph Ω) :
    solutionTreeSet G ≤ᵀ G.edges.1 := by
  classical
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hGb : Nat.RecursiveIn {charFn G.edges.1} fun x => Part.some
      (charFnTot G.edges.1 x) := by
    refine (Nat.RecursiveIn.oracle (O := {charFn G.edges.1})
      (charFn G.edges.1) rfl).of_eq fun x => ?_
    rw [charFn_eq_coe]
    rfl
  have hlen : Primrec fun c : ℕ => (decodeSeq c).length := primrec_seqLength
  -- the boys'-side transcript: at (c, i), the edge bit at (i, entry i's first half)
  have hwqA : Primrec fun m : ℕ => Nat.pair m.unpair.2
      ((decodeSeq m.unpair.1).getD m.unpair.2 0).unpair.1 :=
    Primrec₂.comp (f := Nat.pair) Primrec₂.natPair hsnd
      (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
          hfst hsnd)))
  have htabA := valueTable_recursiveIn_param
    (f := fun c i => charFnTot G.edges.1
      (Nat.pair i ((decodeSeq c).getD i 0).unpair.1))
    (recursiveIn_comp_primrec hGb hwqA)
  have hcl : Nat.RecursiveIn {charFn G.edges.1} fun c => Part.some
      (Nat.pair (id c) (decodeSeq c).length) :=
    recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id)
      (recursiveIn_of_primrec hlen)
  have htabAc : Nat.RecursiveIn {charFn G.edges.1} fun c => Part.some
      (valueTable (fun i => charFnTot G.edges.1
        (Nat.pair i ((decodeSeq c).getD i 0).unpair.1)) (decodeSeq c).length) :=
    (recursiveIn_comp_total htabA hcl).of_eq fun c => by simp only [Nat.unpair_pair, id_eq]
  -- the girls'-side transcript: at (c, i), the edge bit at (entry i's second half, i)
  have hwqB : Primrec fun m : ℕ => Nat.pair
      ((decodeSeq m.unpair.1).getD m.unpair.2 0).unpair.2 m.unpair.2 :=
    Primrec₂.comp (f := Nat.pair) Primrec₂.natPair
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
          hfst hsnd))) hsnd
  have htabB := valueTable_recursiveIn_param
    (f := fun c i => charFnTot G.edges.1
      (Nat.pair ((decodeSeq c).getD i 0).unpair.2 i))
    (recursiveIn_comp_primrec hGb hwqB)
  have htabBc : Nat.RecursiveIn {charFn G.edges.1} fun c => Part.some
      (valueTable (fun i => charFnTot G.edges.1
        (Nat.pair ((decodeSeq c).getD i 0).unpair.2 i)) (decodeSeq c).length) :=
    (recursiveIn_comp_total htabB hcl).of_eq fun c => by simp only [Nat.unpair_pair, id_eq]
  -- package (c, (tableA, tableB)) and verify purely
  have hpack := recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id)
    (recursiveIn_pair_total htabAc htabBc)
  have hpost : Primrec fun z : ℕ =>
      if ((List.range (decodeSeq z.unpair.1).length).map fun i =>
            if (decodeSeq z.unpair.2.unpair.1).getD i 0 ≠ 1 then 1 else 0).findIdx
            (· == 1) = (decodeSeq z.unpair.1).length ∧
          ((List.range (decodeSeq z.unpair.1).length).map fun i =>
            if (decodeSeq z.unpair.2.unpair.2).getD i 0 ≠ 1 then 1 else 0).findIdx
            (· == 1) = (decodeSeq z.unpair.1).length ∧
          ((List.range ((decodeSeq z.unpair.1).length *
              (decodeSeq z.unpair.1).length)).map fun t =>
            if (((decodeSeq z.unpair.1).getD
                    (t / (decodeSeq z.unpair.1).length) 0).unpair.1 =
                  t % (decodeSeq z.unpair.1).length ∧
                ((decodeSeq z.unpair.1).getD
                    (t % (decodeSeq z.unpair.1).length) 0).unpair.2 ≠
                  t / (decodeSeq z.unpair.1).length) ∨
              (((decodeSeq z.unpair.1).getD
                    (t / (decodeSeq z.unpair.1).length) 0).unpair.1 ≠
                  t % (decodeSeq z.unpair.1).length ∧
                ((decodeSeq z.unpair.1).getD
                    (t % (decodeSeq z.unpair.1).length) 0).unpair.2 =
                  t / (decodeSeq z.unpair.1).length)
            then 1 else 0).findIdx (· == 1) =
            (decodeSeq z.unpair.1).length * (decodeSeq z.unpair.1).length
      then 1 else 0 := by
    have hn : Primrec fun z : ℕ => (decodeSeq z.unpair.1).length :=
      primrec_seqLength.comp hfst
    have hgetA : Primrec₂ fun z i : ℕ => (decodeSeq z.unpair.2.unpair.1).getD i 0 :=
      Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
        ((hfst.comp hsnd).comp Primrec.fst) Primrec.snd
    have hgetB : Primrec₂ fun z i : ℕ => (decodeSeq z.unpair.2.unpair.2).getD i 0 :=
      Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
        ((hsnd.comp hsnd).comp Primrec.fst) Primrec.snd
    -- the two components of the grid entry at (z, t)
    have hu₁ : Primrec fun q : ℕ × ℕ =>
        ((decodeSeq q.1.unpair.1).getD (q.2 / (decodeSeq q.1.unpair.1).length) 0).unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp
        (Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
          (hfst.comp Primrec.fst)
          (Primrec.nat_div.comp Primrec.snd (hn.comp Primrec.fst))))
    have hu₂ : Primrec fun q : ℕ × ℕ =>
        ((decodeSeq q.1.unpair.1).getD (q.2 % (decodeSeq q.1.unpair.1).length) 0).unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp
        (Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
          (hfst.comp Primrec.fst)
          (Primrec.nat_mod.comp Primrec.snd (hn.comp Primrec.fst))))
    have hmodz : Primrec fun q : ℕ × ℕ => q.2 % (decodeSeq q.1.unpair.1).length :=
      Primrec.nat_mod.comp Primrec.snd (hn.comp Primrec.fst)
    have hdivz : Primrec fun q : ℕ × ℕ => q.2 / (decodeSeq q.1.unpair.1).length :=
      Primrec.nat_div.comp Primrec.snd (hn.comp Primrec.fst)
    have hlistA : Primrec fun z : ℕ =>
        (List.range (decodeSeq z.unpair.1).length).map fun i =>
          if (decodeSeq z.unpair.2.unpair.1).getD i 0 ≠ 1 then 1 else 0 :=
      Primrec.list_map (Primrec.list_range.comp hn)
        (Primrec.ite (PrimrecPred.not (Primrec.eq.comp hgetA (Primrec.const 1)))
          (Primrec.const 1) (Primrec.const 0))
    have hlistB : Primrec fun z : ℕ =>
        (List.range (decodeSeq z.unpair.1).length).map fun i =>
          if (decodeSeq z.unpair.2.unpair.2).getD i 0 ≠ 1 then 1 else 0 :=
      Primrec.list_map (Primrec.list_range.comp hn)
        (Primrec.ite (PrimrecPred.not (Primrec.eq.comp hgetB (Primrec.const 1)))
          (Primrec.const 1) (Primrec.const 0))
    have hlistC : Primrec fun z : ℕ =>
        (List.range ((decodeSeq z.unpair.1).length *
            (decodeSeq z.unpair.1).length)).map fun t =>
          if (((decodeSeq z.unpair.1).getD
                  (t / (decodeSeq z.unpair.1).length) 0).unpair.1 =
                t % (decodeSeq z.unpair.1).length ∧
              ((decodeSeq z.unpair.1).getD
                  (t % (decodeSeq z.unpair.1).length) 0).unpair.2 ≠
                t / (decodeSeq z.unpair.1).length) ∨
            (((decodeSeq z.unpair.1).getD
                  (t / (decodeSeq z.unpair.1).length) 0).unpair.1 ≠
                t % (decodeSeq z.unpair.1).length ∧
              ((decodeSeq z.unpair.1).getD
                  (t % (decodeSeq z.unpair.1).length) 0).unpair.2 =
                t / (decodeSeq z.unpair.1).length)
          then 1 else 0 :=
      Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hn hn))
        (Primrec.ite (PrimrecPred.or
            (PrimrecPred.and (Primrec.eq.comp hu₁ hmodz)
              (PrimrecPred.not (Primrec.eq.comp hu₂ hdivz)))
            (PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp hu₁ hmodz))
              (Primrec.eq.comp hu₂ hdivz)))
          (Primrec.const 1) (Primrec.const 0))
    exact Primrec.ite (PrimrecPred.and
        (Primrec.eq.comp
          (Primrec.list_findIdx hlistA
            (Primrec.beq.comp Primrec.snd (Primrec.const 1))) hn)
        (PrimrecPred.and
          (Primrec.eq.comp
            (Primrec.list_findIdx hlistB
              (Primrec.beq.comp Primrec.snd (Primrec.const 1))) hn)
          (Primrec.eq.comp
            (Primrec.list_findIdx hlistC
              (Primrec.beq.comp Primrec.snd (Primrec.const 1)))
            (Primrec.nat_mul.comp hn hn))))
      (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpack).of_eq fun c => ?_
  simp only [Nat.unpair_pair, id_eq, decodeSeq_valueTable, charFn]
  -- the verifier accepts exactly the tree nodes
  have hA : ∀ (L : ℕ) (g : ℕ → ℕ),
      (((List.range L).map g).findIdx (· == 1) = L ↔ ∀ j < L, g j ≠ 1) := by
    intro L g
    have key : (((List.range L).map g).findIdx (· == 1) =
        ((List.range L).map g).length) ↔ ∀ j < L, g j ≠ 1 := by
      rw [List.findIdx_eq_length]
      constructor
      · intro h j hj
        have := h (g j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
        simpa using this
      · rintro h x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        simpa using h j (List.mem_range.mp hj)
    rwa [show ((List.range L).map g).length = L from by simp] at key
  have hone : ∀ x : ℕ, charFnTot G.edges.1 x = 1 ↔ x ∈ G.edges.1 := by
    intro x
    by_cases h : x ∈ G.edges.1 <;> simp [charFnTot, h]
  have hsem : (((List.range (decodeSeq c).length).map fun i =>
      if ((List.range (decodeSeq c).length).map fun i' =>
            charFnTot G.edges.1
              (Nat.pair i' ((decodeSeq c).getD i' 0).unpair.1)).getD i 0 ≠ 1
      then 1 else 0).findIdx (· == 1) = (decodeSeq c).length ∧
      ((List.range (decodeSeq c).length).map fun i =>
        if ((List.range (decodeSeq c).length).map fun i' =>
              charFnTot G.edges.1
                (Nat.pair ((decodeSeq c).getD i' 0).unpair.2 i')).getD i 0 ≠ 1
        then 1 else 0).findIdx (· == 1) = (decodeSeq c).length ∧
      ((List.range ((decodeSeq c).length * (decodeSeq c).length)).map fun t =>
        if (((decodeSeq c).getD (t / (decodeSeq c).length) 0).unpair.1 =
              t % (decodeSeq c).length ∧
            ((decodeSeq c).getD (t % (decodeSeq c).length) 0).unpair.2 ≠
              t / (decodeSeq c).length) ∨
          (((decodeSeq c).getD (t / (decodeSeq c).length) 0).unpair.1 ≠
              t % (decodeSeq c).length ∧
            ((decodeSeq c).getD (t % (decodeSeq c).length) 0).unpair.2 =
              t / (decodeSeq c).length)
        then 1 else 0).findIdx (· == 1) =
        (decodeSeq c).length * (decodeSeq c).length) ↔
      SolutionNodeOk G.edges.1 c := by
    rw [solutionNodeOk_iff_grid]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [hA] at h1 h2 h3
      refine ⟨fun i hi => ?_, fun i hi => ?_, fun t ht => ?_⟩
      · have hgi := h1 i hi
        rw [map_range_getD _ hi] at hgi
        by_contra hno
        have hb : charFnTot G.edges.1
            (Nat.pair i ((decodeSeq c).getD i 0).unpair.1) ≠ 1 :=
          fun h => hno ((hone _).mp h)
        exact hgi (by rw [if_pos hb])
      · have hgi := h2 i hi
        rw [map_range_getD _ hi] at hgi
        by_contra hno
        have hb : charFnTot G.edges.1
            (Nat.pair ((decodeSeq c).getD i 0).unpair.2 i) ≠ 1 :=
          fun h => hno ((hone _).mp h)
        exact hgi (by rw [if_pos hb])
      · have hgt := h3 t ht
        by_contra hno
        exact hgt (by rw [if_pos (by tauto)])
    · rintro ⟨h1, h2, h3⟩
      rw [hA, hA, hA]
      refine ⟨fun i hi => ?_, fun i hi => ?_, fun t ht => ?_⟩
      · rw [map_range_getD _ hi]
        rw [if_neg (fun hcon => hcon ((hone _).mpr (h1 i hi)))]
        omega
      · rw [map_range_getD _ hi]
        rw [if_neg (fun hcon => hcon ((hone _).mpr (h2 i hi)))]
        omega
      · rw [if_neg ?_]
        · omega
        · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
          · exact hb ((h3 t ht).mp ha)
          · exact ha ((h3 t ht).mpr hb)
  by_cases hc : c ∈ solutionTreeSet G
  · rw [if_pos (hsem.mpr hc), if_pos hc]
  · rw [if_neg (fun hyes => hc (hsem.mp hyes)), if_neg hc]

/-! ### The path decoder

Reading a path through the partial-solution tree back to the matching: the wife
assigned to boy `a` is the first component of the path's entry at `a` — one
unique-graph lookup per query, then pure unpairing. -/

/-- Layer 1 (raw): the wife the path assigns to boy `a`. -/
noncomputable def pathMatchValue (p : InternalFunction Ω) (a : ℕ) : ℕ :=
  (p.eval a).unpair.1

/-- The graph of the path decoder, as a set of `Nat.pair` codes. -/
def pathMatchGraph (p : InternalFunction Ω) : Set ℕ :=
  {m | pathMatchValue p m.unpair.1 = m.unpair.2}

theorem isGraphOf_pathMatchGraph (p : InternalFunction Ω) :
    IsGraphOf (pathMatchGraph p) (pathMatchValue p) := fun x y => by
  simp [pathMatchGraph, Nat.unpair_pair, Set.mem_setOf_eq]

/-- **The decoder's reduction**: the matching graph is Turing reducible to the path
graph alone — one unique-graph lookup per query, then pure computation. -/
theorem pathMatchGraph_le_graph (p : InternalFunction Ω) :
    pathMatchGraph p ≤ᵀ p.graph.1 := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hval : Nat.RecursiveIn {charFn p.graph.1}
      fun a => Part.some (pathMatchValue p a) :=
    (recursiveIn_comp_total (recursiveIn_of_primrec hfst)
      p.eval_recursiveIn_graph).of_eq fun a => by
        simp only [pathMatchValue]
  have hvfst := recursiveIn_comp_primrec hval hfst
  have hpair := recursiveIn_pair_total hvfst (recursiveIn_of_primrec Primrec.id)
  have hpost : Primrec fun z : ℕ => if z.unpair.1 = z.unpair.2.unpair.2 then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hfst (hsnd.comp hsnd)) (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun m => ?_
  simp only [Nat.unpair_pair, id_eq, charFn]
  by_cases hm : pathMatchValue p m.unpair.1 = m.unpair.2
  · rw [if_pos hm, if_pos (show m ∈ pathMatchGraph p from hm)]
  · rw [if_neg hm, if_neg (show m ∉ pathMatchGraph p from hm)]

/-- Layer 3: the decoded matching as an internal graph-coded function. -/
def pathMatchFunction (h : IsTuringIdeal Ω) (p : InternalFunction Ω) :
    InternalFunction Ω where
  graph := ⟨pathMatchGraph p, h.mem_of_reducible p.graph.2 (pathMatchGraph_le_graph p)⟩
  total x := ⟨pathMatchValue p x, (isGraphOf_pathMatchGraph p x _).mpr rfl⟩
  singleValued x y y' hy hy' :=
    ((isGraphOf_pathMatchGraph p x y).mp hy).symm.trans
      ((isGraphOf_pathMatchGraph p x y').mp hy')

/-- The relational surface of the packaged decoder. -/
theorem pathMatchFunction_mapsTo_iff {h : IsTuringIdeal Ω} {p : InternalFunction Ω}
    {a b : ℕ} : (pathMatchFunction h p).MapsTo a b ↔ (p.eval a).unpair.1 = b :=
  isGraphOf_pathMatchGraph p a b

/-! ### Correctness along the path, and the forward theorem -/

/-- Along a path, every level has a tree node whose entries **are** the path's
values. -/
private theorem path_node_eval {G : InternalLocallyFiniteBigraph Ω}
    {p : InternalFunction Ω} (hp : IsBoundedPathThrough p (solutionTreeSet G))
    (n : ℕ) : ∃ c ∈ solutionTreeSet G, (decodeSeq c).length = n ∧
      ∀ i < n, (decodeSeq c).getD i 0 = p.eval i := by
  obtain ⟨c, hcT, hclen, hagree⟩ := hp n
  exact ⟨c, hcT, hclen, fun i hi => hagree i hi _ (p.pair_eval_mem i)⟩

/-- **Locally finite perfect matching from full finitely-branching Kőnig** over the
Turing-ideal closure conditions — Hirst's forward construction: the partial-solution
tree is internal one reduction below the bare edge set, finitely branching by the two
local-finiteness properties, and infinite by the finite symmetric-Hall covering
lemma; the Kőnig path decodes to the perfect matching. No jump and no reversal
machinery anywhere on this route. -/
theorem locallyFinitePerfectMatchingAt_of_finitelyBranchingKonigAt
    (hΩ : IsTuringIdeal Ω) (hK : FinitelyBranchingKonigAt Ω) :
    LocallyFinitePerfectMatchingAt Ω := by
  intro G hH
  have htree : solutionTreeSet G ∈ Ω :=
    hΩ.mem_of_reducible G.edges.2 (solutionTree_le_graph G)
  obtain ⟨p, hp⟩ := hK
    { tree := ⟨solutionTreeSet G, htree⟩
      prefix_closed := solutionTree_prefix_closed G
      levelwise_bounded := solutionTree_levelwise_bounded G }
    (solutionTree_hasNodeAtEveryLevel G hH)
  refine ⟨pathMatchFunction hΩ p, ?_, ?_, ?_⟩
  · -- edge-respecting: the acquaintance clause at the node one past `a`
    intro a b hab
    rw [pathMatchFunction_mapsTo_iff] at hab
    obtain ⟨c, hcT, hclen, hval⟩ := path_node_eval hp (a + 1)
    have := (hcT.1 a (by omega)).1
    rwa [hval a (by omega), hab] at this
  · -- injectivity: coherence pins the husband of the shared wife
    intro a a' b hab hab'
    rw [pathMatchFunction_mapsTo_iff] at hab hab'
    obtain ⟨c, hcT, hclen, hval⟩ := path_node_eval hp (max (max a a') b + 1)
    have h1 := hcT.2 a (by omega) b (by omega)
    have h2 := hcT.2 a' (by omega) b (by omega)
    rw [hval a (by omega), hval b (by omega)] at h1
    rw [hval a' (by omega), hval b (by omega)] at h2
    have := (h1.mp hab).symm.trans (h2.mp hab')
    omega
  · -- surjectivity: the girl's husband witnesses through coherence
    intro b
    refine ⟨(p.eval b).unpair.2, ?_⟩
    rw [pathMatchFunction_mapsTo_iff]
    obtain ⟨c, hcT, hclen, hval⟩ := path_node_eval hp (max ((p.eval b).unpair.2) b + 1)
    have h1 := hcT.2 ((p.eval b).unpair.2) (by omega) b (by omega)
    rw [hval _ (by omega), hval b (by omega)] at h1
    exact h1.mpr rfl

end ReverseMathlib.Omega
