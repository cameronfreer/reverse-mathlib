/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.RangeSeparation
import ReverseMathlib.Omega.Tree
import ReverseMathlib.Omega.TreeToSystem

/-!
# The tree-to-injections compiler (issue #42, slice 5)

The compiler of the `separation → WKL` direction: from an internal binary tree,
two total injections with globally disjoint ranges whose separating sets compute
paths. For each coded node the **bounded event** is the first stage at which
exactly one child still has a canonical level-`s` extension; the node's common
tag goes into the left-dead or right-dead injection accordingly, and every
non-event input receives a side-specific, input-specific filler.

**Side convention** (pinned): left dead / survivor `1` ⇒ `tag σ ∈ ran f`;
right dead / survivor `0` ⇒ `tag σ ∈ ran g`; a separator (`⊇ ran f`,
`∩ ran g = ∅`) queried at the tag therefore answers `1` exactly when the path
should take bit `1`.

**Coding**: `tag σ = 3σ`; the fillers are `3k + 1` (`f`-side) and `3k + 2`
(`g`-side) at input `k = pair σ s` — residues mod `3` make every cross-class
collision impossible, and first-event uniqueness handles the only same-tag
collision. Totality, injectivity, and disjointness hold for **arbitrary** `T`:
the correctness hypotheses stay out of the data layer.

`hasExt` quantifies over the **canonical level-`s` codes** (the structural
`bitListOfIndex` enumeration), so deciding it takes finitely many stage-bounded
tree queries even for arbitrary `T`; under `IsBinaryTreeCode` this agrees with
unrestricted extension existence. Deadness is monotone above the prefix length
(`(decodeSeq σ).length ≤ s`) — stages below the prefix length are vacuously
absent and never enter the arguments.

**Reuse note**: layer 2 reuses ONLY the finite level-transcript engine
(`levelCodeUpTo`, `levelCodeUpTo_recursiveIn`, `treeLevelList`) from
`ReverseMathlib.Omega.TreeToSystem` — low-level infrastructure computing a
finite level transcript from the tree oracle. No bridge construction and no
direction theorem is consumed (route gates in `scripts/MetaSmoke.lean`).
-/

namespace ReverseMathlib.Omega

namespace TreeSeparation

/-! ### The bounded events, on canonical level codes -/

/-- Node `σ` has a **canonical** level-`s` extension in `T`: some structurally
enumerated length-`s` bit vector lies in `T` and starts with `decodeSeq σ`. -/
def hasExt (T : Set ℕ) (σ s : ℕ) : Prop :=
  ∃ i < 2 ^ s, seqCode (bitListOfIndex s i) ∈ T ∧
    (bitListOfIndex s i).take (decodeSeq σ).length = decodeSeq σ

/-- The code of child `b` of node `σ`. -/
def childCode (σ b : ℕ) : ℕ := seqCode (decodeSeq σ ++ [b])

/-- Child `b` of `σ` is alive at stage `s`. -/
def aliveAt (T : Set ℕ) (σ b s : ℕ) : Prop := hasExt T (childCode σ b) s

/-- Exactly one child of `σ` is alive at stage `s`. -/
def exactlyOne (T : Set ℕ) (σ s : ℕ) : Prop :=
  (aliveAt T σ 0 s ∧ ¬aliveAt T σ 1 s) ∨ (aliveAt T σ 1 s ∧ ¬aliveAt T σ 0 s)

/-- Stage `s` is the **first** stage at which exactly one child of `σ` is
alive. -/
def evtFirst (T : Set ℕ) (σ s : ℕ) : Prop :=
  exactlyOne T σ s ∧ ∀ s' < s, ¬exactlyOne T σ s'

/-- The left-dead event (survivor `1`): the `f`-side. -/
def leftDead (T : Set ℕ) (σ s : ℕ) : Prop := evtFirst T σ s ∧ aliveAt T σ 1 s

/-- The right-dead event (survivor `0`): the `g`-side. -/
def rightDead (T : Set ℕ) (σ s : ℕ) : Prop := evtFirst T σ s ∧ aliveAt T σ 0 s

/-- First stages are unique. -/
theorem evtFirst_unique {T : Set ℕ} {σ s s' : ℕ}
    (h : evtFirst T σ s) (h' : evtFirst T σ s') : s = s' := by
  by_contra hne
  rcases Nat.lt_or_ge s s' with hlt | hge
  · exact h'.2 s hlt h.1
  · exact h.2 s' (by omega) h'.1

/-- The survivor side is determined: no node is both left-dead and right-dead. -/
theorem leftDead_rightDead_disjoint {T : Set ℕ} {σ s s' : ℕ}
    (hl : leftDead T σ s) (hr : rightDead T σ s') : False := by
  obtain rfl := evtFirst_unique hl.1 hr.1
  rcases hl.1.1 with ⟨-, h1⟩ | ⟨-, h0⟩
  · exact h1 hl.2
  · exact h0 hr.2

/-- **Deadness is monotone above the prefix length**: with `T` prefix-closed, a
canonical extension at a later stage truncates to one at any earlier stage that
still accommodates the prefix. -/
theorem hasExt_mono {T : Set ℕ}
    (hclosed : ∀ c ∈ T, ∀ k, seqCode ((decodeSeq c).take k) ∈ T)
    {σ s s' : ℕ} (hlen : (decodeSeq σ).length ≤ s) (hss : s ≤ s')
    (h : hasExt T σ s') : hasExt T σ s := by
  obtain ⟨i, hi, hmem, htake⟩ := h
  have hbits : ∀ x ∈ (bitListOfIndex s' i).take s, x ≤ 1 := fun x hx =>
    isBitSeqCode_seqCode_bitListOfIndex s' i x
      (by rw [decodeSeq_seqCode]; exact List.mem_of_mem_take hx)
  obtain ⟨i', hi', hbl⟩ := exists_bitListOfIndex _ hbits
  rw [List.length_take, min_eq_left (by simpa using hss)] at hi' hbl
  refine ⟨i', hi', ?_, ?_⟩
  · have hmem' := hclosed _ hmem s
    rw [decodeSeq_seqCode, ← hbl] at hmem'
    exact hmem'
  · rw [hbl, List.take_take, min_eq_left hlen, htake]

/-- Below its own length a node has no extension — stages below the prefix
length are vacuously absent. -/
theorem not_hasExt_of_lt {T : Set ℕ} {σ s : ℕ}
    (hs : s < (decodeSeq σ).length) : ¬hasExt T σ s := by
  rintro ⟨i, -, -, htake⟩
  have := congrArg List.length htake
  rw [List.length_take, bitListOfIndex_length] at this
  omega

/-! ### The two injections -/

open Classical in
/-- The `f`-side value at input `k = pair σ s`: the common tag `3σ` on a
left-dead event, the `f`-side filler `3k + 1` otherwise. -/
noncomputable def fval (T : Set ℕ) (k : ℕ) : ℕ :=
  if leftDead T k.unpair.1 k.unpair.2 then 3 * k.unpair.1 else 3 * k + 1

open Classical in
/-- The `g`-side value: the tag `3σ` on a right-dead event, the `g`-side filler
`3k + 2` otherwise. -/
noncomputable def gval (T : Set ℕ) (k : ℕ) : ℕ :=
  if rightDead T k.unpair.1 k.unpair.2 then 3 * k.unpair.1 else 3 * k + 2

/-- Layer 1 (raw): the `f`-injection's graph. -/
noncomputable def fGraph (T : Set ℕ) : Set ℕ :=
  {p | p.unpair.2 = fval T p.unpair.1}

/-- Layer 1 (raw): the `g`-injection's graph. -/
noncomputable def gGraph (T : Set ℕ) : Set ℕ :=
  {p | p.unpair.2 = gval T p.unpair.1}

/-- `fval` is injective — for arbitrary `T`. -/
theorem fval_injective {T : Set ℕ} {k k' : ℕ} (h : fval T k = fval T k') :
    k = k' := by
  classical
  rw [fval, fval] at h
  split_ifs at h with h1 h2 h2
  · have hσ : k.unpair.1 = k'.unpair.1 := by omega
    have hs : k.unpair.2 = k'.unpair.2 :=
      evtFirst_unique (hσ ▸ h1.1) h2.1
    rw [← Nat.pair_unpair k, ← Nat.pair_unpair k', hσ, hs]
  · omega
  · omega
  · omega

/-- `gval` is injective — for arbitrary `T`. -/
theorem gval_injective {T : Set ℕ} {k k' : ℕ} (h : gval T k = gval T k') :
    k = k' := by
  classical
  rw [gval, gval] at h
  split_ifs at h with h1 h2 h2
  · have hσ : k.unpair.1 = k'.unpair.1 := by omega
    have hs : k.unpair.2 = k'.unpair.2 :=
      evtFirst_unique (hσ ▸ h1.1) h2.1
    rw [← Nat.pair_unpair k, ← Nat.pair_unpair k', hσ, hs]
  · omega
  · omega
  · omega

/-- The two value ranges are globally disjoint — for arbitrary `T`: residues
mod `3` kill every cross-class collision, and survivor determinacy kills the
tag–tag case. -/
theorem fval_gval_ne {T : Set ℕ} (k k' : ℕ) : fval T k ≠ gval T k' := by
  classical
  rw [fval, gval]
  split_ifs with h1 h2 h2
  · intro h
    have hσ : k.unpair.1 = k'.unpair.1 := by omega
    exact leftDead_rightDead_disjoint h1 (hσ ▸ h2)
  · omega
  · omega
  · omega

end TreeSeparation

end ReverseMathlib.Omega
