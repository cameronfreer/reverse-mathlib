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

/-! ### Layer 2: relative computability

The only oracle engine is the finite level transcript
(`levelCodeUpTo_recursiveIn`); everything downstream of the transcripts is
primitive recursive. -/

private theorem primrec_snocCodeT : Primrec₂ fun σ b => seqCode (decodeSeq σ ++ [b]) :=
  primrec_seqCode.comp
    (Primrec₂.comp (f := fun (l m : List ℕ) => l ++ m) Primrec.list_append
      (primrec_decodeSeq.comp .fst)
      (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l) Primrec.list_cons
        .snd (.const [])))

private theorem foldr_add_eq_zero_iff' (l : List ℕ) :
    l.foldr (· + ·) 0 = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- Pure: does any member of the decoded level code extend `σ`? (`0`/`1`.) -/
def extBitP (lc σ : ℕ) : ℕ :=
  if ((decodeSeq lc).map fun c =>
      if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1 else 0).foldr
      (· + ·) 0 = 0 then 0 else 1

/-- Pure: exactly one child alive, from the level code. -/
def eoBitP (lc σ : ℕ) : ℕ :=
  if extBitP lc (childCode σ 0) + extBitP lc (childCode σ 1) = 1 then 1 else 0

theorem extBitP_eq_one_iff {T : Set ℕ} {s σ : ℕ} :
    extBitP (seqCode (treeLevelList T s)) σ = 1 ↔ hasExt T σ s := by
  classical
  rw [extBitP, decodeSeq_seqCode]
  constructor
  · intro h
    split_ifs at h with h0
    obtain ⟨x, hx, hxne⟩ : ∃ x ∈ (treeLevelList T s).map fun c =>
        if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1 else 0,
        x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact h0 ((foldr_add_eq_zero_iff' _).mpr hall)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have htake : (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ := by
      by_contra hcon
      rw [if_neg hcon] at hxne
      exact hxne rfl
    obtain ⟨hcT, i, hi, rfl⟩ := mem_treeLevelList_iff.mp hc
    rw [decodeSeq_seqCode] at htake
    exact ⟨i, hi, hcT, htake⟩
  · rintro ⟨i, hi, hmem, htake⟩
    have hc : seqCode (bitListOfIndex s i) ∈ treeLevelList T s :=
      mem_treeLevelList_iff.mpr ⟨hmem, i, hi, rfl⟩
    have hone : (1 : ℕ) ∈ (treeLevelList T s).map fun c =>
        if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1 else 0 :=
      List.mem_map.mpr ⟨_, hc, by rw [decodeSeq_seqCode, if_pos htake]⟩
    have hne : ¬((treeLevelList T s).map fun c =>
        if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1
          else 0).foldr (· + ·) 0 = 0 := fun h0 => by
      simpa using (foldr_add_eq_zero_iff' _).mp h0 1 hone
    rw [if_neg hne]

theorem extBitP_le_one (lc σ : ℕ) : extBitP lc σ ≤ 1 := by
  rw [extBitP]
  split_ifs <;> omega

theorem eoBitP_eq_one_iff {T : Set ℕ} {s σ : ℕ} :
    eoBitP (seqCode (treeLevelList T s)) σ = 1 ↔ exactlyOne T σ s := by
  classical
  have h0 := extBitP_le_one (seqCode (treeLevelList T s)) (childCode σ 0)
  have h1 := extBitP_le_one (seqCode (treeLevelList T s)) (childCode σ 1)
  rw [eoBitP, exactlyOne, aliveAt, aliveAt,
    ← extBitP_eq_one_iff (T := T) (s := s) (σ := childCode σ 0),
    ← extBitP_eq_one_iff (T := T) (s := s) (σ := childCode σ 1)]
  constructor
  · intro h
    by_cases hsum : extBitP (seqCode (treeLevelList T s)) (childCode σ 0)
        + extBitP (seqCode (treeLevelList T s)) (childCode σ 1) = 1
    · omega
    · rw [if_neg hsum] at h
      omega
  · intro hcase
    have hsum : extBitP (seqCode (treeLevelList T s)) (childCode σ 0)
        + extBitP (seqCode (treeLevelList T s)) (childCode σ 1) = 1 := by
      rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    rw [if_pos hsum]

theorem eoBitP_le_one (lc σ : ℕ) : eoBitP lc σ ≤ 1 := by
  rw [eoBitP]
  split_ifs <;> omega

/-- Primitive recursiveness of the pure extension bit. -/
private theorem primrec_extBitP : Primrec₂ extBitP := by
  have hinner : Primrec₂ fun (σ c : ℕ) =>
      if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1 else 0 :=
    (Primrec.ite
      (Primrec.eq.comp
        (Primrec₂.comp (f := fun (n : ℕ) (l : List ℕ) => List.take n l)
          Primrec.list_take
          (Primrec.list_length.comp (primrec_decodeSeq.comp Primrec.fst))
          (primrec_decodeSeq.comp Primrec.snd))
        (primrec_decodeSeq.comp Primrec.fst))
      (.const 1) (.const 0)).to₂
  have hmap : Primrec₂ fun (lc σ : ℕ) =>
      ((decodeSeq lc).map fun c =>
        if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1 else 0) :=
    (Primrec.list_map (primrec_decodeSeq.comp Primrec.fst)
      ((hinner.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)).to₂
  have hsum : Primrec₂ fun (lc σ : ℕ) =>
      ((decodeSeq lc).map fun c =>
        if (decodeSeq c).take (decodeSeq σ).length = decodeSeq σ then 1 else 0).foldr
        (· + ·) 0 :=
    (Primrec.list_foldr (hmap : Primrec _) (.const 0)
      ((Primrec.nat_add.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂)).to₂
  exact (Primrec.ite (Primrec.eq.comp (hsum : Primrec _) (.const 0))
    (.const 0) (.const 1)).to₂

private theorem primrec_eoBitP : Primrec₂ eoBitP := by
  have hchild : ∀ b : ℕ, Primrec fun σ : ℕ => childCode σ b := fun b =>
    primrec_snocCodeT.comp Primrec.id (.const b)
  exact (Primrec.ite (Primrec.eq.comp
    (Primrec.nat_add.comp
      (primrec_extBitP.comp Primrec.fst ((hchild 0).comp Primrec.snd))
      (primrec_extBitP.comp Primrec.fst ((hchild 1).comp Primrec.snd)))
    (.const 1)) (.const 1) (.const 0)).to₂

/-- The level code at stage `s`, relative to the tree — the ONLY reused oracle
engine (`levelCodeUpTo_recursiveIn`, the finite level-transcript computation). -/
private theorem levelCode_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T}
      (fun m => Part.some (levelCodeUpTo T m.unpair.2 (2 ^ m.unpair.2))) := by
  have hpr : Primrec fun m : ℕ => Nat.pair m.unpair.2 (2 ^ m.unpair.2) :=
    Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair)
      (Primrec₂.comp (f := fun (a b : ℕ) => a ^ b)
        (Primrec₂.unpaired'.mp Nat.Primrec.pow) (.const 2)
        (Primrec.snd.comp Primrec.unpair))
  exact (recursiveIn_comp_primrec (levelCodeUpTo_recursiveIn T) hpr).of_eq fun m => by
    simp [Nat.unpair_pair]

/-- The stage-indexed exactly-one bit, relative to the tree (`m = pair σ s`). -/
private theorem eo_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T} (fun m => Part.some
      (eoBitP (levelCodeUpTo T m.unpair.2 (2 ^ m.unpair.2)) m.unpair.1)) := by
  have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair (levelCode_recursiveIn T)
  have hpost : Nat.Partrec fun z => Part.some
      (eoBitP z.unpair.2 z.unpair.1.unpair.1) := by
    have : Primrec fun z : ℕ => eoBitP z.unpair.2 z.unpair.1.unpair.1 :=
      primrec_eoBitP.comp (Primrec.snd.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  exact (hpost.recursiveIn.comp hpair).of_eq fun m => by
    simp [Seq.seq, Nat.unpair_pair]

/-- The alive-`1` bit at the input's own stage, relative to the tree. -/
private theorem a1_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T} (fun k => Part.some
      (extBitP (levelCodeUpTo T k.unpair.2 (2 ^ k.unpair.2))
        (childCode k.unpair.1 1))) := by
  have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair (levelCode_recursiveIn T)
  have hpost : Nat.Partrec fun z => Part.some
      (extBitP z.unpair.2 (childCode z.unpair.1.unpair.1 1)) := by
    have : Primrec fun z : ℕ =>
        extBitP z.unpair.2 (childCode z.unpair.1.unpair.1 1) :=
      primrec_extBitP.comp (Primrec.snd.comp Primrec.unpair)
        ((primrec_snocCodeT.comp Primrec.id (.const 1)).comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  exact (hpost.recursiveIn.comp hpair).of_eq fun m => by
    simp [Seq.seq, Nat.unpair_pair]

/-- The stage-table of exactly-one bits below the input's own stage. -/
private theorem eoTable_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T} (fun k => Part.some
      (valueTable (fun s' => eoBitP (levelCodeUpTo T s' (2 ^ s'))
        k.unpair.1) (k.unpair.2 + 1))) := by
  have hf := valueTable_recursiveIn_param
    (f := fun σ s' => eoBitP (levelCodeUpTo T s' (2 ^ s')) σ)
    ((eo_recursiveIn T).of_eq fun m => rfl)
  have hpr : Primrec fun k : ℕ => Nat.pair k.unpair.1 (k.unpair.2 + 1) :=
    Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
  exact (recursiveIn_comp_primrec hf hpr).of_eq fun k => by
    simp [Nat.unpair_pair]

/-- The pure left-dead decision from the table and the alive-`1` bit. -/
def leftDeadBitP (s tbl a1 : ℕ) : ℕ :=
  if (decodeSeq tbl).getD s 0 = 1 ∧
      ((decodeSeq tbl).take s).foldr (· + ·) 0 = 0 ∧ a1 = 1 then 1 else 0

/-- The right-side decision: identical shape with the alive-`0` bit. -/
def rightDeadBitP (s tbl a0 : ℕ) : ℕ :=
  if (decodeSeq tbl).getD s 0 = 1 ∧
      ((decodeSeq tbl).take s).foldr (· + ·) 0 = 0 ∧ a0 = 1 then 1 else 0

/-- **The decision bridge**: on the genuine table and alive bit, the pure
left-dead decision computes exactly the `leftDead` event. -/
theorem leftDeadBitP_eq_one_iff {T : Set ℕ} {σ s : ℕ} :
    leftDeadBitP s
      (valueTable (fun s' => eoBitP (levelCodeUpTo T s' (2 ^ s')) σ) (s + 1))
      (extBitP (levelCodeUpTo T s (2 ^ s)) (childCode σ 1)) = 1 ↔
    leftDead T σ s := by
  classical
  rw [leftDeadBitP]
  have htblget : (decodeSeq (valueTable (fun s' =>
      eoBitP (levelCodeUpTo T s' (2 ^ s')) σ) (s + 1))).getD s 0
      = eoBitP (levelCodeUpTo T s (2 ^ s)) σ := by
    rw [decodeSeq_valueTable, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp), Option.getD_some]
    simp
  have htbltake : (decodeSeq (valueTable (fun s' =>
      eoBitP (levelCodeUpTo T s' (2 ^ s')) σ) (s + 1))).take s
      = (List.range s).map fun s' => eoBitP (levelCodeUpTo T s' (2 ^ s')) σ := by
    rw [decodeSeq_valueTable, ← List.map_take, List.take_range,
      min_eq_left (by omega)]
  rw [htblget, htbltake, ← seqCode_treeLevelList T s]
  constructor
  · intro h
    split_ifs at h with hc
    · obtain ⟨h1, h0, ha1⟩ := hc
      refine ⟨⟨eoBitP_eq_one_iff.mp h1, fun s' hs' hone => ?_⟩,
        extBitP_eq_one_iff.mp ha1⟩
      have hmem : eoBitP (levelCodeUpTo T s' (2 ^ s')) σ ∈
          (List.range s).map fun s'' => eoBitP (levelCodeUpTo T s'' (2 ^ s'')) σ :=
        List.mem_map.mpr ⟨s', List.mem_range.mpr hs', rfl⟩
      have hz := (foldr_add_eq_zero_iff' _).mp h0 _ hmem
      rw [← seqCode_treeLevelList] at hz
      rw [← eoBitP_eq_one_iff (T := T) (s := s') (σ := σ)] at hone
      omega
  · rintro ⟨⟨hone, hmin⟩, halive⟩
    have hmid : ((List.range s).map fun s' =>
        eoBitP (levelCodeUpTo T s' (2 ^ s')) σ).foldr (· + ·) 0 = 0 := by
      refine (foldr_add_eq_zero_iff' _).mpr fun x hx => ?_
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hs'
      have hno := hmin s' hs'
      rw [← eoBitP_eq_one_iff (T := T) (s := s') (σ := σ)] at hno
      have := eoBitP_le_one (seqCode (treeLevelList T s')) σ
      rw [seqCode_treeLevelList] at this hno
      omega
    rw [if_pos ⟨eoBitP_eq_one_iff.mpr hone, hmid, extBitP_eq_one_iff.mpr halive⟩]

/-- The right-side decision bridge — the mirror. -/
theorem rightDeadBitP_eq_one_iff {T : Set ℕ} {σ s : ℕ} :
    rightDeadBitP s
      (valueTable (fun s' => eoBitP (levelCodeUpTo T s' (2 ^ s')) σ) (s + 1))
      (extBitP (levelCodeUpTo T s (2 ^ s)) (childCode σ 0)) = 1 ↔
    rightDead T σ s := by
  classical
  rw [rightDeadBitP]
  have htblget : (decodeSeq (valueTable (fun s' =>
      eoBitP (levelCodeUpTo T s' (2 ^ s')) σ) (s + 1))).getD s 0
      = eoBitP (levelCodeUpTo T s (2 ^ s)) σ := by
    rw [decodeSeq_valueTable, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp), Option.getD_some]
    simp
  have htbltake : (decodeSeq (valueTable (fun s' =>
      eoBitP (levelCodeUpTo T s' (2 ^ s')) σ) (s + 1))).take s
      = (List.range s).map fun s' => eoBitP (levelCodeUpTo T s' (2 ^ s')) σ := by
    rw [decodeSeq_valueTable, ← List.map_take, List.take_range,
      min_eq_left (by omega)]
  rw [htblget, htbltake, ← seqCode_treeLevelList T s]
  constructor
  · intro h
    split_ifs at h with hc
    · obtain ⟨h1, h0, ha0⟩ := hc
      refine ⟨⟨eoBitP_eq_one_iff.mp h1, fun s' hs' hone => ?_⟩,
        extBitP_eq_one_iff.mp ha0⟩
      have hmem : eoBitP (levelCodeUpTo T s' (2 ^ s')) σ ∈
          (List.range s).map fun s'' => eoBitP (levelCodeUpTo T s'' (2 ^ s'')) σ :=
        List.mem_map.mpr ⟨s', List.mem_range.mpr hs', rfl⟩
      have hz := (foldr_add_eq_zero_iff' _).mp h0 _ hmem
      rw [← seqCode_treeLevelList] at hz
      rw [← eoBitP_eq_one_iff (T := T) (s := s') (σ := σ)] at hone
      omega
  · rintro ⟨⟨hone, hmin⟩, halive⟩
    have hmid : ((List.range s).map fun s' =>
        eoBitP (levelCodeUpTo T s' (2 ^ s')) σ).foldr (· + ·) 0 = 0 := by
      refine (foldr_add_eq_zero_iff' _).mpr fun x hx => ?_
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hs'
      have hno := hmin s' hs'
      rw [← eoBitP_eq_one_iff (T := T) (s := s') (σ := σ)] at hno
      have := eoBitP_le_one (seqCode (treeLevelList T s')) σ
      rw [seqCode_treeLevelList] at this hno
      omega
    rw [if_pos ⟨eoBitP_eq_one_iff.mpr hone, hmid, extBitP_eq_one_iff.mpr halive⟩]

private theorem primrec_leftDeadBitP :
    Primrec fun z : ℕ × ℕ × ℕ => leftDeadBitP z.1 z.2.1 z.2.2 := by
  have htbl : Primrec fun z : ℕ × ℕ × ℕ => decodeSeq z.2.1 :=
    primrec_decodeSeq.comp (Primrec.fst.comp Primrec.snd)
  exact Primrec.ite
    ((PrimrecPred.and
      (Primrec.eq.comp ((Primrec.list_getD 0).comp htbl Primrec.fst) (.const 1))
      (PrimrecPred.and
        (Primrec.eq.comp
          (Primrec.list_foldr
            (Primrec₂.comp (f := fun (n : ℕ) (l : List ℕ) => List.take n l)
              Primrec.list_take Primrec.fst htbl)
            (.const 0)
            ((Primrec.nat_add.comp (Primrec.fst.comp .snd)
              (Primrec.snd.comp .snd)).to₂))
          (.const 0))
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (.const 1)))))
    (.const 1) (.const 0)

private theorem primrec_rightDeadBitP :
    Primrec fun z : ℕ × ℕ × ℕ => rightDeadBitP z.1 z.2.1 z.2.2 := by
  have h := primrec_leftDeadBitP
  exact h.of_eq fun z => rfl

/-- The `f`-value as an oracle computation: the event table and the alive bit
from the transcripts, then the pure decision. -/
theorem fval_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T} (fun k => Part.some (fval T k)) := by
  classical
  have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair ((eoTable_recursiveIn T).pair (a1_recursiveIn T))
  have hpost : Nat.Partrec fun z => Part.some
      (if leftDeadBitP z.unpair.1.unpair.2 z.unpair.2.unpair.1
          z.unpair.2.unpair.2 = 1
        then 3 * z.unpair.1.unpair.1 else 3 * z.unpair.1 + 1) := by
    have hld : Primrec fun z : ℕ =>
        leftDeadBitP z.unpair.1.unpair.2 z.unpair.2.unpair.1 z.unpair.2.unpair.2 :=
      (primrec_leftDeadBitP.comp (Primrec.pair
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp Primrec.unpair)))))).of_eq fun z => rfl
    have hval : Primrec fun z : ℕ =>
        if leftDeadBitP z.unpair.1.unpair.2 z.unpair.2.unpair.1
            z.unpair.2.unpair.2 = 1
          then 3 * z.unpair.1.unpair.1 else 3 * z.unpair.1 + 1 :=
      Primrec.ite (Primrec.eq.comp hld (.const 1))
        (Primrec.nat_mul.comp (.const 3)
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (Primrec.succ.comp (Primrec.nat_mul.comp (.const 3)
          (Primrec.fst.comp Primrec.unpair)))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun k => ?_
  simp only [Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  rw [fval]
  by_cases hld : leftDead T k.unpair.1 k.unpair.2
  · rw [if_pos hld, if_pos (leftDeadBitP_eq_one_iff.mpr hld)]
  · rw [if_neg hld, if_neg fun hbit => hld (leftDeadBitP_eq_one_iff.mp hbit)]

/-- The `g`-value as an oracle computation — the mirror with the alive-`0` bit. -/
theorem gval_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T} (fun k => Part.some (gval T k)) := by
  classical
  have ha0 : Nat.RecursiveIn {charFn T} (fun k => Part.some
      (extBitP (levelCodeUpTo T k.unpair.2 (2 ^ k.unpair.2))
        (childCode k.unpair.1 0))) := by
    have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
      ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
    have hpair := hid.pair (levelCode_recursiveIn T)
    have hpost : Nat.Partrec fun z => Part.some
        (extBitP z.unpair.2 (childCode z.unpair.1.unpair.1 0)) := by
      have : Primrec fun z : ℕ =>
          extBitP z.unpair.2 (childCode z.unpair.1.unpair.1 0) :=
        primrec_extBitP.comp (Primrec.snd.comp Primrec.unpair)
          ((primrec_snocCodeT.comp Primrec.id (.const 0)).comp
            (Primrec.fst.comp (Primrec.unpair.comp
              (Primrec.fst.comp Primrec.unpair))))
      exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
    exact (hpost.recursiveIn.comp hpair).of_eq fun m => by
      simp [Seq.seq, Nat.unpair_pair]
  have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair ((eoTable_recursiveIn T).pair ha0)
  have hpost : Nat.Partrec fun z => Part.some
      (if rightDeadBitP z.unpair.1.unpair.2 z.unpair.2.unpair.1
          z.unpair.2.unpair.2 = 1
        then 3 * z.unpair.1.unpair.1 else 3 * z.unpair.1 + 2) := by
    have hrd : Primrec fun z : ℕ =>
        rightDeadBitP z.unpair.1.unpair.2 z.unpair.2.unpair.1 z.unpair.2.unpair.2 :=
      (primrec_rightDeadBitP.comp (Primrec.pair
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp Primrec.unpair)))))).of_eq fun z => rfl
    have hval : Primrec fun z : ℕ =>
        if rightDeadBitP z.unpair.1.unpair.2 z.unpair.2.unpair.1
            z.unpair.2.unpair.2 = 1
          then 3 * z.unpair.1.unpair.1 else 3 * z.unpair.1 + 2 :=
      Primrec.ite (Primrec.eq.comp hrd (.const 1))
        (Primrec.nat_mul.comp (.const 3)
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 3)
          (Primrec.fst.comp Primrec.unpair)) (.const 2))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun k => ?_
  simp only [Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  rw [gval]
  by_cases hrd : rightDead T k.unpair.1 k.unpair.2
  · rw [if_pos hrd, if_pos (rightDeadBitP_eq_one_iff.mpr hrd)]
  · rw [if_neg hrd, if_neg fun hbit => hrd (rightDeadBitP_eq_one_iff.mp hbit)]

/-- **Layer 2 headline**: the `f`-injection's graph reduces to the tree. -/
theorem fGraph_le_tree (T : Set ℕ) : fGraph T ≤ᵀ T := by
  classical
  have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hfv := recursiveIn_comp_primrec (fval_recursiveIn T)
    (Primrec.fst.comp Primrec.unpair)
  have hpair := hid.pair hfv
  have hpost : Nat.Partrec fun z => Part.some
      (if z.unpair.1.unpair.2 = z.unpair.2 then 1 else 0) := by
    have hval : Primrec fun z : ℕ =>
        if z.unpair.1.unpair.2 = z.unpair.2 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases h : p.unpair.2 = fval T p.unpair.1
  · rw [if_pos h, if_pos (show p ∈ fGraph T from h)]
  · rw [if_neg h, if_neg (show p ∉ fGraph T from h)]

/-- **Layer 2 headline**: the `g`-injection's graph reduces to the tree. -/
theorem gGraph_le_tree (T : Set ℕ) : gGraph T ≤ᵀ T := by
  classical
  have hid : Nat.RecursiveIn {charFn T} fun m => Part.some m :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hgv := recursiveIn_comp_primrec (gval_recursiveIn T)
    (Primrec.fst.comp Primrec.unpair)
  have hpair := hid.pair hgv
  have hpost : Nat.Partrec fun z => Part.some
      (if z.unpair.1.unpair.2 = z.unpair.2 then 1 else 0) := by
    have hval : Primrec fun z : ℕ =>
        if z.unpair.1.unpair.2 = z.unpair.2 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases h : p.unpair.2 = gval T p.unpair.1
  · rw [if_pos h, if_pos (show p ∈ gGraph T from h)]
  · rw [if_neg h, if_neg (show p ∉ gGraph T from h)]

end TreeSeparation

open TreeSeparation in
/-- **Layer 3**: the `f`-injection as an internal graph-coded function. -/
noncomputable def treeSepF {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (T : Ω.InternalSet) : InternalFunction Ω where
  graph := ⟨fGraph T.1, h.mem_of_reducible T.2 (fGraph_le_tree T.1)⟩
  total := fun k => ⟨fval T.1 k, show (Nat.pair k (fval T.1 k)).unpair.2
    = fval T.1 (Nat.pair k (fval T.1 k)).unpair.1 by rw [Nat.unpair_pair]⟩
  singleValued := fun k v v' hv hv' => by
    have h1 : v = fval T.1 k := by
      have h' : (Nat.pair k v).unpair.2 = fval T.1 (Nat.pair k v).unpair.1 := hv
      rwa [Nat.unpair_pair] at h'
    have h2 : v' = fval T.1 k := by
      have h' : (Nat.pair k v').unpair.2 = fval T.1 (Nat.pair k v').unpair.1 := hv'
      rwa [Nat.unpair_pair] at h'
    rw [h1, h2]

open TreeSeparation in
/-- **Layer 3**: the `g`-injection as an internal graph-coded function. -/
noncomputable def treeSepG {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (T : Ω.InternalSet) : InternalFunction Ω where
  graph := ⟨gGraph T.1, h.mem_of_reducible T.2 (gGraph_le_tree T.1)⟩
  total := fun k => ⟨gval T.1 k, show (Nat.pair k (gval T.1 k)).unpair.2
    = gval T.1 (Nat.pair k (gval T.1 k)).unpair.1 by rw [Nat.unpair_pair]⟩
  singleValued := fun k v v' hv hv' => by
    have h1 : v = gval T.1 k := by
      have h' : (Nat.pair k v).unpair.2 = gval T.1 (Nat.pair k v).unpair.1 := hv
      rwa [Nat.unpair_pair] at h'
    have h2 : v' = gval T.1 k := by
      have h' : (Nat.pair k v').unpair.2 = gval T.1 (Nat.pair k v').unpair.1 := hv'
      rwa [Nat.unpair_pair] at h'
    rw [h1, h2]

open TreeSeparation in
theorem treeSepF_mapsTo_iff {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {T : Ω.InternalSet} {k v : ℕ} :
    (treeSepF h T).MapsTo k v ↔ v = fval T.1 k := by
  change (Nat.pair k v).unpair.2 = fval T.1 (Nat.pair k v).unpair.1 ↔ _
  rw [Nat.unpair_pair]

open TreeSeparation in
theorem treeSepG_mapsTo_iff {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {T : Ω.InternalSet} {k v : ℕ} :
    (treeSepG h T).MapsTo k v ↔ v = gval T.1 k := by
  change (Nat.pair k v).unpair.2 = gval T.1 (Nat.pair k v).unpair.1 ↔ _
  rw [Nat.unpair_pair]

open TreeSeparation in
/-- The compiled `f`-injection is injective. -/
theorem treeSepF_isInjective {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (T : Ω.InternalSet) : (treeSepF h T).IsInjective := fun _ _ _ hm hm' =>
  fval_injective ((treeSepF_mapsTo_iff.mp hm).symm.trans
    (treeSepF_mapsTo_iff.mp hm'))

open TreeSeparation in
/-- The compiled `g`-injection is injective. -/
theorem treeSepG_isInjective {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (T : Ω.InternalSet) : (treeSepG h T).IsInjective := fun _ _ _ hm hm' =>
  gval_injective ((treeSepG_mapsTo_iff.mp hm).symm.trans
    (treeSepG_mapsTo_iff.mp hm'))

open TreeSeparation in
/-- The compiled injections have globally disjoint ranges. -/
theorem treeSep_disjointRanges {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (T : Ω.InternalSet) : DisjointRanges (treeSepF h T) (treeSepG h T) :=
  fun m m' _ hm hm' =>
    fval_gval_ne m m' ((treeSepF_mapsTo_iff.mp hm).symm.trans
      (treeSepG_mapsTo_iff.mp hm'))

end ReverseMathlib.Omega
