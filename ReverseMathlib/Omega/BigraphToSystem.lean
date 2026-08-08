/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.RadixCoding
import ReverseMathlib.Omega.Bigraph
import ReverseMathlib.Omega.FiniteMatching
import ReverseMathlib.Omega.TreeToSystem

/-!
# `bigraphToSystem`: the paired mate-table compiler (issue #42, slice 2)

The compiler of the `EFILCω → 2-regular matchingω` direction, following Shafer's
Lemma 6.1.7 at `m = 1` and layered exactly as the earlier compilers: (1) raw
table construction; (2) relative-computability theorem; (3) packaging; (4)
mathematical correctness.

A level-`n` node is a **paired mate table**: a length-`n` list whose entry `k`
is `Nat.pair y x` — `y` the right mate selected for left vertex `k`, `x` the left
mate selected for right vertex `k` — with the source's consistency condition
inside the frontier: the right mate of left `k` is `l` exactly when the left mate
of right `l` is `k`, for `k, l` below the level. Choices are structurally
enumerated: digit `k` of a radix-4 index selects one of the two enumerated
neighbors on each side, so a mate table is determined by an index below `4 ^ n`
and the two enumerator transcripts (`valueTable`).

Acceptance criteria:

* the fiber graph is Turing-reducible to the **join of the two enumerator
  graphs** — the enumerators enter only through their finite transcripts, and the
  common edge set never enters the computation (it is correctness-only, through
  the two `mem_iff` fields);
* the bonding graph is `treeBondingGraph`, reused **verbatim**;
* level nonemptiness comes from the finite symmetric-Hall covering lemma
  (`exists_matching_covering` + `hall_of_degree_le_two`) — never from any
  infinite matching theorem;
* the decoder's raw graph mentions only the section graph.
-/

namespace ReverseMathlib.Omega

/-! ### Layer 1 (raw): mate tables from digits and transcripts -/

/-- The radix-4 digit list of index `i`: digit `k` selects the level-`k` mate pair. -/
def mateDigits (n i : ℕ) : List ℕ := digitListOfIndex (List.replicate n 4) i

@[simp]
theorem mateDigits_length (n i : ℕ) : (mateDigits n i).length = n := by
  rw [mateDigits, digitListOfIndex_length, List.length_replicate]

theorem mateDigits_take (n i : ℕ) :
    (mateDigits (n + 1) i).take n = mateDigits n (i % 4 ^ n) := by
  rw [mateDigits, mateDigits, digitListOfIndex_take, List.take_replicate,
    min_eq_left (Nat.le_succ n), List.prod_replicate]

theorem mateDigits_injOn {n : ℕ} : Set.InjOn (mateDigits n) {i | i < 4 ^ n} := by
  intro i hi i' hi' hEq
  have hprod : (List.replicate n 4).prod = 4 ^ n := List.prod_replicate n 4
  exact digitListOfIndex_injOn (by simpa [hprod] using hi)
    (by simpa [hprod] using hi') hEq

theorem mateDigits_lt {n i k : ℕ} (hk : k < n) : (mateDigits n i).getD k 0 < 4 := by
  have hfa : List.Forall₂ (· < ·) (mateDigits n i) (List.replicate n 4) :=
    digitListOfIndex_forall₂_lt (by simp +contextual) i
  have hlen : (mateDigits n i).length = n := mateDigits_length n i
  have := List.forall₂_iff_get.mp hfa
  have hget := this.2 k (by omega) (by simpa using hk)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simpa using hget

/-- **Completeness of the digit enumeration**: any sequence of per-level choices
below 4 is realized by an index below `4 ^ n`. -/
theorem exists_mateDigits {l : List ℕ} (hlen : ∀ x ∈ l, x < 4) :
    ∃ i < 4 ^ l.length, mateDigits l.length i = l := by
  have hfa : List.Forall₂ (· < ·) l (List.replicate l.length 4) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun k h₁ h₂ => ?_⟩
    simpa using hlen l[k] (List.getElem_mem h₁)
  obtain ⟨i, hi, hdi⟩ := exists_digitListOfIndex hfa
  rw [List.prod_replicate] at hi
  exact ⟨i, hi, by rw [mateDigits, hdi]⟩

/-- The mate pair selected by digit `d < 4` from the two decoded neighbor rows:
`d % 2` indexes the left row (the right mate), `d / 2` the right row (the left
mate). -/
def mateEntry (lrow rrow d : ℕ) : ℕ :=
  Nat.pair ((decodeSeq lrow).getD (d % 2) 0) ((decodeSeq rrow).getD (d / 2) 0)

/-- The level-`n` mate table for transcripts `lt`, `rt` and index `i`. -/
def mateTable (lt rt n i : ℕ) : List ℕ :=
  (List.range n).map fun k =>
    mateEntry ((decodeSeq lt).getD k 0) ((decodeSeq rt).getD k 0)
      ((mateDigits n i).getD k 0)

@[simp]
theorem mateTable_length (lt rt n i : ℕ) : (mateTable lt rt n i).length = n := by
  simp [mateTable]

theorem mateTable_getD {lt rt n i k : ℕ} (hk : k < n) :
    (mateTable lt rt n i).getD k 0 =
      mateEntry ((decodeSeq lt).getD k 0) ((decodeSeq rt).getD k 0)
        ((mateDigits n i).getD k 0) := by
  rw [mateTable, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hk), Option.getD_some]
  simp

/-- **The bonding normal form**: truncating a level-`n + 1` mate table built from
level-`n + 1` transcripts lands exactly on the level-`n` table built from the
level-`n` transcripts at the reduced index — transcript prefixes agree entrywise. -/
theorem mateTable_take (lam rho : ℕ → ℕ) (n i : ℕ) :
    (mateTable (valueTable lam (n + 1)) (valueTable rho (n + 1)) (n + 1) i).take n
      = mateTable (valueTable lam n) (valueTable rho n) n (i % 4 ^ n) := by
  rw [mateTable, mateTable, ← List.map_take, List.take_range,
    min_eq_left (Nat.le_succ n)]
  refine List.map_congr_left fun k hk => ?_
  have hkn : k < n := List.mem_range.mp hk
  have h1 : (decodeSeq (valueTable lam (n + 1))).getD k 0
      = (decodeSeq (valueTable lam n)).getD k 0 := by
    rw [decodeSeq_valueTable, decodeSeq_valueTable, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using by omega),
      List.getElem?_eq_getElem (by simpa using hkn)]
    simp
  have h2 : (decodeSeq (valueTable rho (n + 1))).getD k 0
      = (decodeSeq (valueTable rho n)).getD k 0 := by
    rw [decodeSeq_valueTable, decodeSeq_valueTable, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using by omega),
      List.getElem?_eq_getElem (by simpa using hkn)]
    simp
  have h3 : (mateDigits (n + 1) i).getD k 0 = (mateDigits n (i % 4 ^ n)).getD k 0 := by
    rw [← mateDigits_take]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hkn]
  rw [h1, h2, h3]

/-! ### The consistency verifier, numerically -/

/-- The number of frontier-consistency violations of a coded mate table: pairs
`k, l` below the length where "the right mate of left `k` is `l`" and "the left
mate of right `l` is `k`" disagree. Zero exactly on consistent tables. -/
def mateBadCount (c : ℕ) : ℕ :=
  ((List.range ((decodeSeq c).length * (decodeSeq c).length)).map fun m =>
    let k := m / (decodeSeq c).length
    let l := m % (decodeSeq c).length
    if ((decodeSeq c).getD k 0).unpair.1 = l
      then (if ((decodeSeq c).getD l 0).unpair.2 = k then 0 else 1)
      else (if ((decodeSeq c).getD l 0).unpair.2 = k then 1 else 0)).foldr (· + ·) 0

/-- Frontier consistency, propositionally. -/
def MateConsistent (tbl : List ℕ) : Prop :=
  ∀ k < tbl.length, ∀ l < tbl.length,
    ((tbl.getD k 0).unpair.1 = l ↔ (tbl.getD l 0).unpair.2 = k)

theorem foldr_add_eq_zero_iff (l : List ℕ) :
    l.foldr (· + ·) 0 = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem mateBadCount_eq_zero_iff {tbl : List ℕ} :
    mateBadCount (seqCode tbl) = 0 ↔ MateConsistent tbl := by
  rw [mateBadCount, foldr_add_eq_zero_iff, decodeSeq_seqCode]
  constructor
  · intro h k hk l hl
    have hm : k * tbl.length + l ∈ List.range (tbl.length * tbl.length) := by
      rw [List.mem_range]
      calc k * tbl.length + l < k * tbl.length + tbl.length := by omega
        _ = (k + 1) * tbl.length := (Nat.succ_mul k tbl.length).symm
        _ ≤ tbl.length * tbl.length := Nat.mul_le_mul_right tbl.length (by omega)
    have := h _ (List.mem_map.mpr ⟨k * tbl.length + l, hm, rfl⟩)
    have hdiv : (k * tbl.length + l) / tbl.length = k := by
      rw [Nat.mul_comm k tbl.length, Nat.mul_add_div (by omega : 0 < tbl.length),
        Nat.div_eq_of_lt hl]
      omega
    have hmod : (k * tbl.length + l) % tbl.length = l := by
      rw [Nat.mul_comm k tbl.length, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
    rw [hdiv, hmod] at this
    constructor
    · intro h1
      by_contra h2
      rw [if_pos h1, if_neg h2] at this
      omega
    · intro h2
      by_contra h1
      rw [if_neg h1, if_pos h2] at this
      omega
  · intro h x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hm
    have hlen : 0 < tbl.length := by
      rcases Nat.eq_zero_or_pos tbl.length with h0 | h0
      · rw [h0] at hm
        omega
      · exact h0
    have hk : m / tbl.length < tbl.length := Nat.div_lt_of_lt_mul hm
    have hl : m % tbl.length < tbl.length := Nat.mod_lt _ hlen
    have hiff := h _ hk _ hl
    by_cases h1 : (tbl.getD (m / tbl.length) 0).unpair.1 = m % tbl.length
    · rw [if_pos h1, if_pos (hiff.mp h1)]
    · rw [if_neg h1, if_neg fun h2 => h1 (hiff.mpr h2)]

/-! ### The level list -/

/-- The level-`n` fiber list: the codes of all consistent mate tables for the
level-`n` transcripts, structurally enumerated below `4 ^ n`. -/
def mateLevelList (lam rho : ℕ → ℕ) (n : ℕ) : List ℕ :=
  ((List.range (4 ^ n)).map fun i =>
    seqCode (mateTable (valueTable lam n) (valueTable rho n) n i)).filter
    fun c => mateBadCount c = 0

theorem mem_mateLevelList_iff {lam rho : ℕ → ℕ} {n c : ℕ} :
    c ∈ mateLevelList lam rho n ↔
      mateBadCount c = 0 ∧ ∃ i < 4 ^ n,
        c = seqCode (mateTable (valueTable lam n) (valueTable rho n) n i) := by
  simp only [mateLevelList, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hbad⟩
    exact ⟨hbad, i, hi, rfl⟩
  · rintro ⟨hbad, i, hi, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hbad⟩

/-- Layer 1 (raw): the fiber graph — `Nat.pair n c` for `c` the code of the
level-`n` list of consistent mate tables. -/
def mateFiberGraph (lam rho : ℕ → ℕ) : Set ℕ :=
  {p | ∃ n, p = Nat.pair n (seqCode (mateLevelList lam rho n))}

theorem mem_mateFiberGraph_iff {lam rho : ℕ → ℕ} {p : ℕ} :
    p ∈ mateFiberGraph lam rho ↔
      p.unpair.2 = seqCode (mateLevelList lam rho p.unpair.1) := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [Nat.unpair_pair]
  · intro h
    exact ⟨p.unpair.1, by rw [← h, Nat.pair_unpair]⟩

end ReverseMathlib.Omega
