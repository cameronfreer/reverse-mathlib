/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.KleeneTree

/-!
# The Kleene tree's diagonal property: exact path characterization (issue #76)

The existing Kleene tree (`ReverseMathlib.Omega.KleeneTree`, unchanged here, with its
coding and mathlib's `Nat.Partrec.Code` numbering) is characterized by one exact property
of its paths:

> `P` is a path through the Kleene tree **iff** the characteristic bit of `P` at every `e`
> disagrees, **modulo 2**, with every convergent diagonal value `φ_e(e)`.

`DiagonallyDisagreesMod2 P` names the right-hand side with the *unbounded* evaluator
`Nat.Partrec.Code.eval`; the tree's constraint speaks about the *step-bounded*
`diagObserved`. The two directions cross that gap in the two ways the evaluator allows:

* **path → disagreement** (`diagonallyDisagreesMod2_of_isBinaryPathThrough`):
  `evaln_complete` gives a step bound, `evaln_mono` lifts it to a length covering both
  the bound and `e + 1`, and the path's node at that length carries the constraint;
* **disagreement → path** (`isBinaryPathThrough_of_diagonallyDisagreesMod2`): each finite
  characteristic-bit prefix of `P` is built **directly** (`charPrefix`) and shown to be a
  node, its constraints discharged by `evaln_sound`. No compactness and no path-existence
  theorem is used.

**The `% 2` convention is the tree's, kept explicit.** Conventional binary DNR requires
disagreement with `v` itself, which restricts a binary output only when `v < 2`;
disagreement with `v % 2` restricts it always. The two properties are different, and their
conversion is a separate program (umbrella #75) — nothing here claims it.

**Corollary** (`not_recursiveSet_of_diagonallyDisagreesMod2`): no recursive set has the
property — derived from the existing no-recursive-path theorem through the converse
direction, and gated to reach it. A restatement of what the tree already proves, in the
property's own terms; not a new registered fact, and no atlas registration or scoreboard
change is made here. No relativization: the oracle-relative tree is a later child of #75
and will need its own numbering translation.
-/

namespace ReverseMathlib.Omega

open Nat.Partrec (Code)

open Classical in
/-- **The modulo-2 diagonal-disagreement property**: the characteristic bit of `P` at `e`
differs from `v % 2` for every value `v` of the convergent diagonal computation `φ_e(e)`
(mathlib's numbering, unbounded evaluation). -/
def DiagonallyDisagreesMod2 (P : Set ℕ) : Prop :=
  ∀ e v : ℕ, v ∈ (Denumerable.ofNat Code e).eval e → (if e ∈ P then 1 else 0) ≠ v % 2

/-! ### Path → disagreement -/

open Classical in
/-- A node of a path through the Kleene tree, at a length beyond `e`, has bit `e` equal
to the characteristic bit of the path. -/
theorem getD_eq_charBit_of_path {P : Set ℕ} {c n e : ℕ} (hcT : c ∈ kleeneTree)
    (hlen : (decodeSeq c).length = n)
    (hagree : ∀ i < n, ((decodeSeq c).getD i 0 = 1 ↔ i ∈ P)) (he : e < n) :
    (decodeSeq c).getD e 0 = if e ∈ P then 1 else 0 := by
  have hle : (decodeSeq c).getD e 0 ≤ 1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact he),
      Option.getD_some]
    exact hcT.1 _ (List.getElem_mem _)
  by_cases hPe : e ∈ P
  · rw [if_pos hPe]
    exact (hagree e he).mpr hPe
  · rw [if_neg hPe]
    have : (decodeSeq c).getD e 0 ≠ 1 := fun h => hPe ((hagree e he).mp h)
    omega

/-- **Path → disagreement.** -/
theorem diagonallyDisagreesMod2_of_isBinaryPathThrough {P : Set ℕ}
    (hpath : IsBinaryPathThrough P kleeneTree) : DiagonallyDisagreesMod2 P := by
  intro e v hv
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  set n := max k (e + 1) with hn
  have hobs : diagObserved n e = some v :=
    Nat.Partrec.Code.evaln_mono (le_max_left _ _) hk
  have hen : e < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨c, hcT, hlen, hagree⟩ := hpath n
  have hne : (decodeSeq c).getD e 0 ≠ v % 2 :=
    hcT.2 e (by rw [hlen]; exact hen) v (by rw [hlen]; exact hobs)
  rwa [getD_eq_charBit_of_path hcT hlen hagree hen] at hne

/-! ### Disagreement → path -/

open Classical in
/-- The length-`n` characteristic-bit prefix of `P`. -/
noncomputable def charPrefix (P : Set ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map fun i => if i ∈ P then 1 else 0

@[simp] theorem length_charPrefix (P : Set ℕ) (n : ℕ) : (charPrefix P n).length = n := by
  simp [charPrefix]

open Classical in
theorem getD_charPrefix {P : Set ℕ} {n i : ℕ} (hi : i < n) :
    (charPrefix P n).getD i 0 = if i ∈ P then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
    Option.getD_some]
  simp [charPrefix]

/-- Every characteristic-bit prefix of a diagonally disagreeing set is a node of the
Kleene tree: bit-valued by construction, and each observed diagonal value is a value of
the unbounded evaluation (`evaln_sound`), so the property discharges the constraint. -/
theorem charPrefix_mem_kleeneTree {P : Set ℕ} (h : DiagonallyDisagreesMod2 P) (n : ℕ) :
    seqCode (charPrefix P n) ∈ kleeneTree := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [decodeSeq_seqCode] at hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> simp
  · intro e he v hv
    rw [decodeSeq_seqCode] at he hv ⊢
    rw [length_charPrefix] at he hv
    rw [getD_charPrefix he]
    exact h e v (Nat.Partrec.Code.evaln_sound hv)

/-- **Disagreement → path**: the characteristic-bit prefixes themselves are the nodes; no
compactness or path-existence theorem is used. -/
theorem isBinaryPathThrough_of_diagonallyDisagreesMod2 {P : Set ℕ}
    (h : DiagonallyDisagreesMod2 P) : IsBinaryPathThrough P kleeneTree := by
  intro n
  refine ⟨seqCode (charPrefix P n), charPrefix_mem_kleeneTree h n, by simp, ?_⟩
  intro i hi
  rw [decodeSeq_seqCode, getD_charPrefix hi]
  by_cases hPi : i ∈ P <;> simp [hPi]

/-! ### The exact characterization and the obstruction corollary -/

/-- **The exact path characterization of the Kleene tree.** -/
theorem isBinaryPathThrough_kleeneTree_iff (P : Set ℕ) :
    IsBinaryPathThrough P kleeneTree ↔ DiagonallyDisagreesMod2 P :=
  ⟨diagonallyDisagreesMod2_of_isBinaryPathThrough,
    isBinaryPathThrough_of_diagonallyDisagreesMod2⟩

/-- **No recursive set has the modulo-2 diagonal-disagreement property** — derived from the
existing no-recursive-path theorem through the converse direction of the
characterization. -/
theorem not_recursiveSet_of_diagonallyDisagreesMod2 {P : Set ℕ}
    (h : DiagonallyDisagreesMod2 P) : ¬ RecursiveSet P :=
  fun hP => not_isBinaryPathThrough_of_recursiveSet hP
    (isBinaryPathThrough_of_diagonallyDisagreesMod2 h)

/-- Equivalently: every path through the Kleene tree is non-recursive. -/
theorem not_recursiveSet_of_isBinaryPathThrough_kleeneTree {P : Set ℕ}
    (hpath : IsBinaryPathThrough P kleeneTree) : ¬ RecursiveSet P :=
  fun hP => not_isBinaryPathThrough_of_recursiveSet hP hpath

end ReverseMathlib.Omega
