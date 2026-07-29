/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.List
import ReverseMathlib.Standard.Trees
import ReverseMathlib.Standard.InverseLimit

/-!
# Weak Kőnig and explicit finite inverse-limit compactness: relative bridges

The two ambient-Lean factorizations `weakKonig_of_efilc` and `efilc_of_weakKonig`, each taking
its principle as a hypothesis and never deriving it. As with the Hall slice, both principles
are provable outright in Lean, so the informative artifacts are the proof terms — certified by
dependency assertions in `scripts/MetaSmoke.lean` — not the implications as propositions. No
RCA₀, ω-model, or subsystem claim is made or implied.

* `weakKonig_of_efilc`: levels of a binary tree are explicitly finite once enumerated, so a
  binary tree with nodes at every level yields an explicit finite inverse system of encoded
  level nodes whose sections are paths. Encoding into `ℕ` happens here and only here, per the
  representation contract of `ReverseMathlib.Standard.Trees`.
* `efilc_of_weakKonig`: an explicit finite inverse system embeds into a binary tree by chunk
  coding — level `n` contributes a chunk of `(F.fiber n).card` bits, decoded by binary value
  modulo the fiber's cardinality (every bit pattern decodes to a valid rank, so chunk validity
  is automatic); tree membership demands only coherence of adjacent decoded ranks under the
  bonding maps. Finite descending chains through the system supply nodes at every level; a
  path's decoded ranks form a section.

Quantitative cost note: chunk width `c n = (F.fiber n).card` is deliberately simple, total,
and auditable — and intentionally inefficient. The construction works verbatim for any widths
`w` with `(F.fiber n).card ≤ 2 ^ w n` (e.g. `w n = ⌈log₂ card⌉`, or a supplied code-width
bound); the current choice is the easy instance. The quantitative track (Q8/Q9) generalizes
the width parameter rather than optimizing this proof.
-/

assert_not_exists nonempty_sections_of_finite_inverse_system
assert_not_exists exists_seq_forall_proj_of_forall_finite

namespace ReverseMathlib.Slice

open ReverseMathlib.Standard

/-! ## Bit-chunk coding -/

/-- Little-endian binary value of a bit list. -/
def bitsVal (l : List Bool) : ℕ :=
  l.foldr (fun b acc => 2 * acc + b.toNat) 0

@[simp]
theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp]
theorem bitsVal_cons (b : Bool) (l : List Bool) :
    bitsVal (b :: l) = 2 * bitsVal l + b.toNat := rfl

/-- The `w` low-order bits of `v`, little-endian. -/
def natToBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: natToBits w (v / 2)

@[simp]
theorem length_natToBits (w v : ℕ) : (natToBits w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [natToBits, ih]

theorem mod_two_pow_succ (v w : ℕ) : v % 2 ^ (w + 1) = 2 * (v / 2 % 2 ^ w) + v % 2 := by
  have hp : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
  have h4 : v / 2 % 2 ^ w < 2 ^ w := Nat.mod_lt _ hp
  have h5 : v % 2 < 2 := Nat.mod_lt _ (by omega)
  conv_lhs => rw [← Nat.div_add_mod v 2]
  rw [pow_succ, mul_comm ((2 : ℕ) ^ w) 2, Nat.add_mod, Nat.mul_mod_mul_left]
  have h6 : v % 2 % (2 * 2 ^ w) = v % 2 := Nat.mod_eq_of_lt (by omega)
  rw [h6, Nat.mod_eq_of_lt (by omega)]

theorem bitsVal_natToBits (w v : ℕ) : bitsVal (natToBits w v) = v % 2 ^ w := by
  induction w generalizing v with
  | zero => simp [natToBits, Nat.mod_one]
  | succ w ih =>
    simp only [natToBits, bitsVal_cons, ih, mod_two_pow_succ]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> simp

/-- Extract the chunk of width `w` starting at `s`. -/
def chunkAt (l : List Bool) (s w : ℕ) : List Bool :=
  (l.drop s).take w

/-- Complete chunks are stable under appending. -/
theorem chunkAt_append {l t : List Bool} {s w : ℕ} (h : s + w ≤ l.length) :
    chunkAt (l ++ t) s w = chunkAt l s w := by
  unfold chunkAt
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
  simp only [List.length_drop]
  omega

/-- Complete chunks are stable under truncation. -/
theorem chunkAt_take {l : List Bool} {s w k : ℕ} (h : s + w ≤ k) :
    chunkAt (l.take k) s w = chunkAt l s w := by
  unfold chunkAt
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Cumulative chunk widths: `widthSum c n = c 0 + ⋯ + c (n-1)`. -/
def widthSum (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => widthSum c n + c n

theorem widthSum_mono (c : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) : widthSum c m ≤ widthSum c n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · have : m = n + 1 := by omega
      subst this
      exact le_refl _

theorem le_widthSum (c : ℕ → ℕ) (hc : ∀ i, 0 < c i) (n : ℕ) : n ≤ widthSum c n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have := hc n
    simp only [widthSum]
    omega

/-- The concatenated chunk list for ranks `r` with widths `c`, up to level `m`. -/
def chunkList (c r : ℕ → ℕ) : ℕ → List Bool
  | 0 => []
  | m + 1 => chunkList c r m ++ natToBits (c m) (r m)

@[simp]
theorem length_chunkList (c r : ℕ → ℕ) (m : ℕ) : (chunkList c r m).length = widthSum c m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [chunkList, widthSum, ih]

theorem chunkAt_chunkList (c r : ℕ → ℕ) {i m : ℕ} (h : i < m) :
    chunkAt (chunkList c r m) (widthSum c i) (c i) = natToBits (c i) (r i) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with h' | h'
    · rw [chunkList, chunkAt_append (by
        rw [length_chunkList]
        exact widthSum_mono c (show i + 1 ≤ m from h'))]
      exact ih h'
    · have : i = m := by omega
      subst this
      change ((chunkList c r i ++ natToBits (c i) (r i)).drop (widthSum c i)).take (c i) = _
      rw [show widthSum c i = (chunkList c r i).length from (length_chunkList c r i).symm,
        List.drop_left, List.take_of_length_le (by simp)]

/-! ## Direction: EFILC from weak Kőnig -/

/-- Finite descending chains of an explicit finite inverse system: from any element of any
fiber, a coherent chain runs all the way down. (A *global* coherent chain is exactly what EFILC
asserts; finite ones are free.) -/
theorem exists_chain (F : ExplicitFiniteInverseSystem) :
    ∀ (m : ℕ) (x : ℕ), x ∈ F.fiber m → ∃ y : ℕ → ℕ,
      y m = x ∧ (∀ i, i ≤ m → y i ∈ F.fiber i) ∧
      ∀ i, i < m → ∀ h : y (i + 1) ∈ F.fiber (i + 1),
        (F.restrict i ⟨y (i + 1), h⟩ : {z // z ∈ F.fiber i}).val = y i := by
  intro m
  induction m with
  | zero =>
    intro x hx
    refine ⟨fun _ => x, rfl, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    exact hx
  | succ m ih =>
    intro x hx
    obtain ⟨y, hym, hmem, hcoh⟩ :=
      ih (F.restrict m ⟨x, hx⟩).val (F.restrict m ⟨x, hx⟩).property
    classical
    refine ⟨Function.update y (m + 1) x, by simp, ?_, ?_⟩
    · intro i hi
      rcases eq_or_ne i (m + 1) with h | h
      · subst h
        simpa using hx
      · rw [Function.update_of_ne h]
        exact hmem i (by omega)
    · intro i hi h
      rcases eq_or_ne i m with hi' | hi'
      · subst hi'
        have hsub : (⟨Function.update y (i + 1) x (i + 1), h⟩ :
            {z // z ∈ F.fiber (i + 1)}) = ⟨x, hx⟩ :=
          Subtype.ext (Function.update_self _ _ _)
        rw [hsub, Function.update_of_ne (show i ≠ i + 1 by omega)]
        exact hym.symm
      · have hne1 : i + 1 ≠ m + 1 := by omega
        have hne2 : i ≠ m + 1 := by omega
        have hmemy : y (i + 1) ∈ F.fiber (i + 1) := by
          have h' := h
          rwa [Function.update_of_ne hne1] at h'
        have hsub : (⟨Function.update y (m + 1) x (i + 1), h⟩ :
            {z // z ∈ F.fiber (i + 1)}) = ⟨y (i + 1), hmemy⟩ :=
          Subtype.ext (Function.update_of_ne hne1 _ _)
        rw [hsub, Function.update_of_ne hne2]
        exact hcoh i (by omega) hmemy

/-- **EFILC from weak Kőnig**, an ambient-Lean factorization: the hypothesis is never derived.
The system embeds into a binary tree by chunk coding with decode-by-modulo, so chunk validity
is automatic and only adjacent-rank coherence constrains membership. -/
theorem efilc_of_weakKonig (hwk : WeakKonig) : ExplicitFiniteInverseLimitCompactness := by
  intro F
  classical
  set c : ℕ → ℕ := fun n => (F.fiber n).card with hcdef
  have hcpos : ∀ n, 0 < c n := fun n => Finset.card_pos.mpr (F.nonempty n)
  let elem : ∀ n, Fin (c n) ≃o {x // x ∈ F.fiber n} := fun n => (F.fiber n).orderIsoOfFin rfl
  let elemVal : ℕ → ℕ → ℕ := fun n v => (elem n ⟨v % c n, Nat.mod_lt _ (hcpos n)⟩).val
  have elemVal_mem : ∀ n v, elemVal n v ∈ F.fiber n := fun n v =>
    (elem n ⟨v % c n, Nat.mod_lt _ (hcpos n)⟩).property
  let rank : List Bool → ℕ → ℕ := fun l n => bitsVal (chunkAt l (widthSum c n) (c n))
  let T : Set (List Bool) := {l | ∀ n, widthSum c (n + 2) ≤ l.length →
    (F.restrict n ⟨elemVal (n + 1) (rank l (n + 1)), elemVal_mem _ _⟩ :
      {z // z ∈ F.fiber n}).val = elemVal n (rank l n)}
  have hTtree : IsTree T := by
    intro l a hl n hn
    have hlen : widthSum c (n + 2) ≤ l.length := hn
    have e1 : rank (l ++ [a]) (n + 1) = rank l (n + 1) := by
      change bitsVal (chunkAt (l ++ [a]) (widthSum c (n + 1)) (c (n + 1))) = _
      rw [chunkAt_append (show widthSum c (n + 1) + c (n + 1) ≤ l.length from hlen)]
    have e2 : rank (l ++ [a]) n = rank l n := by
      change bitsVal (chunkAt (l ++ [a]) (widthSum c n) (c n)) = _
      rw [chunkAt_append
        (le_trans (widthSum_mono c (show n + 1 ≤ n + 2 by omega)) hlen)]
    have hcond : widthSum c (n + 2) ≤ (l ++ [a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    have := hl n hcond
    rwa [e1, e2] at this
  have hTlev : HasNodeAtEveryLevel T := by
    intro L
    obtain ⟨x, hx⟩ := F.nonempty L
    obtain ⟨y, -, hymem, hycoh⟩ := exists_chain F L x hx
    set r : ℕ → ℕ := fun i =>
      if h : i ≤ L then (((elem i).symm ⟨y i, hymem i h⟩ : Fin (c i)) : ℕ) else 0 with hrdef
    have hrEq : ∀ i, (h : i ≤ L) →
        r i = (((elem i).symm ⟨y i, hymem i h⟩ : Fin (c i)) : ℕ) := by
      intro i h
      simp only [hrdef]
      rw [dif_pos h]
    have hrlt : ∀ i, i ≤ L → r i < c i := by
      intro i h
      rw [hrEq i h]
      exact ((elem i).symm ⟨y i, hymem i h⟩).isLt
    have hrdec : ∀ i, (h : i ≤ L) → elemVal i (r i % 2 ^ c i) = y i := by
      intro i h
      have h1 : r i < c i := hrlt i h
      have h2 : c i < 2 ^ c i := Nat.lt_two_pow_self
      have hinner : r i % 2 ^ c i = r i := Nat.mod_eq_of_lt (by omega)
      have hmod : r i % 2 ^ c i % c i = r i := by
        rw [hinner, Nat.mod_eq_of_lt h1]
      change (elem i ⟨r i % 2 ^ c i % c i, Nat.mod_lt _ (hcpos i)⟩).val = y i
      have hfin : (⟨r i % 2 ^ c i % c i, Nat.mod_lt _ (hcpos i)⟩ : Fin (c i)) =
          (elem i).symm ⟨y i, hymem i h⟩ := by
        apply Fin.ext
        change r i % 2 ^ c i % c i = _
        rw [hmod, hrEq i h]
      exact (congrArg (fun z : Fin (c i) => ((elem i) z).val) hfin).trans
        (congrArg Subtype.val ((elem i).apply_symm_apply _))
    have hnodeRank : ∀ i, i < L → rank (chunkList c r L) i = r i % 2 ^ c i := by
      intro i hi
      change bitsVal (chunkAt (chunkList c r L) (widthSum c i) (c i)) = _
      rw [chunkAt_chunkList c r hi, bitsVal_natToBits]
    have hnodeT : chunkList c r L ∈ T := by
      intro n hn
      rw [length_chunkList] at hn
      have hnL : n + 1 < L := by
        by_contra hcon
        have hcon' : L ≤ n + 1 := by omega
        have h1 := widthSum_mono c hcon'
        have h3 := hcpos (n + 1)
        have hunf : widthSum c (n + 2) = widthSum c (n + 1) + c (n + 1) := rfl
        omega
      have hv1 : elemVal (n + 1) (rank (chunkList c r L) (n + 1)) = y (n + 1) := by
        rw [hnodeRank (n + 1) hnL]
        exact hrdec (n + 1) (by omega)
      have hv0 : elemVal n (rank (chunkList c r L) n) = y n := by
        rw [hnodeRank n (by omega)]
        exact hrdec n (by omega)
      have hsub : (⟨elemVal (n + 1) (rank (chunkList c r L) (n + 1)), elemVal_mem _ _⟩ :
          {z // z ∈ F.fiber (n + 1)}) = ⟨y (n + 1), hymem (n + 1) (by omega)⟩ :=
        Subtype.ext hv1
      rw [hsub, hv0]
      exact hycoh n (by omega) _
    refine ⟨(chunkList c r L).take L, hTtree.take_mem hnodeT L, ?_⟩
    rw [List.length_take, length_chunkList]
    have := le_widthSum c hcpos L
    omega
  obtain ⟨p, hp⟩ := hwk T hTtree hTlev
  choose W hWT hWlen hWp using hp
  set s : ℕ → ℕ := fun n => elemVal n (rank (W (widthSum c (n + 2))) n) with hsdef
  have hs_mem : ∀ n, s n ∈ F.fiber n := fun n => elemVal_mem _ _
  have hWtake : ∀ n, W (widthSum c (n + 2)) =
      (W (widthSum c (n + 3))).take (widthSum c (n + 2)) := by
    intro n
    apply eq_of_matches_path
    · rw [hWlen, List.length_take, hWlen]
      have := widthSum_mono c (show n + 2 ≤ n + 3 by omega)
      omega
    · exact hWp _
    · intro i hi
      rw [List.getElem_take]
      exact hWp _ i _
  refine ⟨s, hs_mem, ?_⟩
  intro n
  have hlenW : widthSum c (n + 2) ≤ (W (widthSum c (n + 3))).length := by
    rw [hWlen]
    exact widthSum_mono c (by omega)
  have hcohW := hWT (widthSum c (n + 3)) n hlenW
  have hr1 : rank (W (widthSum c (n + 2))) n = rank (W (widthSum c (n + 3))) n := by
    rw [hWtake n]
    change bitsVal (chunkAt ((W (widthSum c (n + 3))).take (widthSum c (n + 2)))
      (widthSum c n) (c n)) = _
    rw [chunkAt_take (widthSum_mono (c := c) (m := n + 1) (n := n + 2) (by omega))]
  change (F.restrict n ⟨s (n + 1), hs_mem (n + 1)⟩ : {z // z ∈ F.fiber n}).val = s n
  have hsub : (⟨s (n + 1), hs_mem (n + 1)⟩ : {z // z ∈ F.fiber (n + 1)}) =
      ⟨elemVal (n + 1) (rank (W (widthSum c (n + 3))) (n + 1)), elemVal_mem _ _⟩ := rfl
  rw [hsub, hcohW]
  change elemVal n (rank (W (widthSum c (n + 3))) n) =
    elemVal n (rank (W (widthSum c (n + 2))) n)
  exact congrArg (elemVal n) hr1.symm

/-! ## Direction: weak Kőnig from EFILC -/

/-- All bit lists of length `n`, explicitly enumerated. -/
def allBitLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => ((allBitLists n) ×ˢ (Finset.univ : Finset Bool)).image fun p => p.1 ++ [p.2]

theorem mem_allBitLists : ∀ {n : ℕ} {l : List Bool}, l ∈ allBitLists n ↔ l.length = n
  | 0, l => by
    constructor
    · intro h
      rw [allBitLists, Finset.mem_singleton] at h
      simp [h]
    · intro h
      rw [allBitLists, Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero h
  | n + 1, l => by
    rw [allBitLists, Finset.mem_image]
    constructor
    · rintro ⟨⟨l', b⟩, hp, rfl⟩
      rw [Finset.mem_product] at hp
      have := mem_allBitLists.mp hp.1
      simp [this]
    · intro hlen
      have hne : l ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
      refine ⟨(l.dropLast, l.getLast hne), ?_, List.dropLast_append_getLast hne⟩
      rw [Finset.mem_product]
      exact ⟨mem_allBitLists.mpr (by simp [hlen]), Finset.mem_univ _⟩

/-- Decode a natural back to a bit list (total, via a default). -/
def decodeBits (x : ℕ) : List Bool :=
  (Encodable.decode (α := List Bool) x).getD []

@[simp]
theorem decodeBits_encode (l : List Bool) : decodeBits (Encodable.encode l) = l := by
  simp [decodeBits]

/-- **Weak Kőnig from EFILC**, an ambient-Lean factorization: the hypothesis is never derived.
Levels of the binary tree are explicitly enumerated `Finset`s of encoded nodes; the encoding
into `ℕ` happens here, inside the bridge, per the representation contract. -/
theorem weakKonig_of_efilc (hc : ExplicitFiniteInverseLimitCompactness) : WeakKonig := by
  intro T hT hlev
  classical
  let level : ℕ → Finset (List Bool) := fun n => (allBitLists n).filter (· ∈ T)
  have mem_level : ∀ {n l}, l ∈ level n ↔ l ∈ T ∧ l.length = n := by
    intro n l
    simp only [level, Finset.mem_filter, mem_allBitLists]
    tauto
  let F : ExplicitFiniteInverseSystem :=
    { fiber := fun n => (level n).image Encodable.encode
      restrict := fun n x => ⟨Encodable.encode ((decodeBits x.1).take n), by
        obtain ⟨l, hl, hlx⟩ := Finset.mem_image.mp x.2
        obtain ⟨hlT, hllen⟩ := mem_level.mp hl
        refine Finset.mem_image.mpr ⟨l.take n, mem_level.mpr ⟨hT.take_mem hlT n, ?_⟩, ?_⟩
        · rw [List.length_take, hllen]
          omega
        · rw [← hlx, decodeBits_encode]⟩
      nonempty := fun n => by
        obtain ⟨l, hl, hlen⟩ := hlev n
        exact (show (level n).Nonempty from ⟨l, mem_level.mpr ⟨hl, hlen⟩⟩).image _ }
  obtain ⟨s, hs, hcoh⟩ := hc F
  have hdec : ∀ n, decodeBits (s n) ∈ level n ∧ Encodable.encode (decodeBits (s n)) = s n := by
    intro n
    obtain ⟨l, hl, hlx⟩ := Finset.mem_image.mp (hs n)
    rw [← hlx, decodeBits_encode]
    exact ⟨hl, rfl⟩
  set L : ℕ → List Bool := fun n => decodeBits (s n) with hL
  have hLmem : ∀ n, L n ∈ T := fun n => (mem_level.mp (hdec n).1).1
  have hLlen : ∀ n, (L n).length = n := fun n => (mem_level.mp (hdec n).1).2
  have hLtake : ∀ n, (L (n + 1)).take n = L n := by
    intro n
    have hcohn : Encodable.encode ((decodeBits (s (n + 1))).take n) = s n := hcoh n
    have h2 : Encodable.encode (L n) = s n := (hdec n).2
    exact Encodable.encode_injective (hcohn.trans h2.symm)
  exact exists_path_of_coherent_chain L hLmem hLlen hLtake

end ReverseMathlib.Slice
