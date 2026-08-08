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

/-! ### Layer 2: relative computability

The level code is a **pure** function of the two enumerator transcripts — no
oracle loop: the oracles are consulted exactly to build the two `valueTable`s,
and everything after is primitive recursive. -/

/-- Append one entry to a coded sequence — primitive recursive. (Private mirror of
the earlier compilers' helper, which is file-private there.) -/
private theorem primrec_snocCode'' : Primrec₂ fun ih x => seqCode (decodeSeq ih ++ [x]) :=
  primrec_seqCode.comp
    (Primrec₂.comp (f := fun (l m : List ℕ) => l ++ m) Primrec.list_append
      (primrec_decodeSeq.comp .fst)
      (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l) Primrec.list_cons
        .snd (.const [])))

private theorem primrec_replicate4 : Primrec fun n => List.replicate n 4 := by
  have h : Primrec fun n => (List.range n).map fun _ => (4 : ℕ) :=
    Primrec.list_map Primrec.list_range (Primrec₂.const 4)
  exact h.of_eq fun n => by simp

/-- The candidate mate-table code, primitive recursive in the packed
`Nat.pair lt (Nat.pair rt (Nat.pair n i))`. -/
private theorem primrec_mateTableCode :
    Primrec fun q : ℕ => seqCode (mateTable q.unpair.1 q.unpair.2.unpair.1
      q.unpair.2.unpair.2.unpair.1 q.unpair.2.unpair.2.unpair.2) := by
  have hlt : Primrec fun q : ℕ => q.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hrt : Primrec fun q : ℕ => q.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hn : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hi : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hdig : Primrec fun q : ℕ =>
      mateDigits q.unpair.2.unpair.2.unpair.1 q.unpair.2.unpair.2.unpair.2 :=
    Primrec₂.comp (f := digitListOfIndex) primrec_digitListOfIndex
      (primrec_replicate4.comp hn) hi
  have hd : Primrec₂ fun (q k : ℕ) =>
      (mateDigits q.unpair.2.unpair.2.unpair.1 q.unpair.2.unpair.2.unpair.2).getD
        k 0 :=
    ((Primrec.list_getD 0).comp (hdig.comp Primrec.fst) Primrec.snd).to₂
  have hrow1 : Primrec fun qk : ℕ × ℕ => (decodeSeq qk.1.unpair.1).getD qk.2 0 :=
    Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
      (hlt.comp Primrec.fst) Primrec.snd
  have hrow2 : Primrec fun qk : ℕ × ℕ =>
      (decodeSeq qk.1.unpair.2.unpair.1).getD qk.2 0 :=
    Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
      (hrt.comp Primrec.fst) Primrec.snd
  have he1 : Primrec fun qk : ℕ × ℕ =>
      (decodeSeq ((decodeSeq qk.1.unpair.1).getD qk.2 0)).getD
        ((mateDigits qk.1.unpair.2.unpair.2.unpair.1
          qk.1.unpair.2.unpair.2.unpair.2).getD qk.2 0 % 2) 0 :=
    Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
      hrow1 (Primrec.nat_mod.comp hd (Primrec.const 2))
  have he2 : Primrec fun qk : ℕ × ℕ =>
      (decodeSeq ((decodeSeq qk.1.unpair.2.unpair.1).getD qk.2 0)).getD
        ((mateDigits qk.1.unpair.2.unpair.2.unpair.1
          qk.1.unpair.2.unpair.2.unpair.2).getD qk.2 0 / 2) 0 :=
    Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
      hrow2 (Primrec.nat_div.comp hd (Primrec.const 2))
  have hentry : Primrec₂ fun (q k : ℕ) =>
      mateEntry ((decodeSeq q.unpair.1).getD k 0)
        ((decodeSeq q.unpair.2.unpair.1).getD k 0)
        ((mateDigits q.unpair.2.unpair.2.unpair.1
          q.unpair.2.unpair.2.unpair.2).getD k 0) := by
    have h := Primrec₂.natPair.comp he1 he2
    exact h.to₂.of_eq fun q k => rfl
  have htbl : Primrec fun q : ℕ =>
      (List.range q.unpair.2.unpair.2.unpair.1).map fun k =>
        mateEntry ((decodeSeq q.unpair.1).getD k 0)
          ((decodeSeq q.unpair.2.unpair.1).getD k 0)
          ((mateDigits q.unpair.2.unpair.2.unpair.1
            q.unpair.2.unpair.2.unpair.2).getD k 0) :=
    Primrec.list_map (Primrec.list_range.comp hn) hentry
  exact (primrec_seqCode.comp htbl).of_eq fun q => rfl

private theorem primrec_mateBadCount : Primrec mateBadCount := by
  have hlen : Primrec fun c : ℕ => (decodeSeq c).length := primrec_seqLength
  have hL : Primrec fun c : ℕ =>
      List.range ((decodeSeq c).length * (decodeSeq c).length) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp hlen hlen)
  have hk : Primrec fun cm : ℕ × ℕ => cm.2 / (decodeSeq cm.1).length :=
    Primrec.nat_div.comp .snd (hlen.comp .fst)
  have hl : Primrec fun cm : ℕ × ℕ => cm.2 % (decodeSeq cm.1).length :=
    Primrec.nat_mod.comp .snd (hlen.comp .fst)
  have hu1 : Primrec fun cm : ℕ × ℕ =>
      ((decodeSeq cm.1).getD (cm.2 / (decodeSeq cm.1).length) 0).unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
        .fst hk))
  have hu2 : Primrec fun cm : ℕ × ℕ =>
      ((decodeSeq cm.1).getD (cm.2 % (decodeSeq cm.1).length) 0).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
        .fst hl))
  have hinner : Primrec₂ fun (c m : ℕ) =>
      if ((decodeSeq c).getD (m / (decodeSeq c).length) 0).unpair.1
          = m % (decodeSeq c).length
        then (if ((decodeSeq c).getD (m % (decodeSeq c).length) 0).unpair.2
            = m / (decodeSeq c).length then 0 else 1)
        else (if ((decodeSeq c).getD (m % (decodeSeq c).length) 0).unpair.2
            = m / (decodeSeq c).length then 1 else 0) :=
    (Primrec.ite (Primrec.eq.comp hu1 hl)
      (Primrec.ite (Primrec.eq.comp hu2 hk) (.const 0) (.const 1))
      (Primrec.ite (Primrec.eq.comp hu2 hk) (.const 1) (.const 0))).to₂
  have hmap : Primrec fun c : ℕ =>
      (List.range ((decodeSeq c).length * (decodeSeq c).length)).map fun m =>
        if ((decodeSeq c).getD (m / (decodeSeq c).length) 0).unpair.1
            = m % (decodeSeq c).length
          then (if ((decodeSeq c).getD (m % (decodeSeq c).length) 0).unpair.2
              = m / (decodeSeq c).length then 0 else 1)
          else (if ((decodeSeq c).getD (m % (decodeSeq c).length) 0).unpair.2
              = m / (decodeSeq c).length then 1 else 0) :=
    Primrec.list_map hL hinner
  have hfold : Primrec fun c : ℕ =>
      ((List.range ((decodeSeq c).length * (decodeSeq c).length)).map fun m =>
        if ((decodeSeq c).getD (m / (decodeSeq c).length) 0).unpair.1
            = m % (decodeSeq c).length
          then (if ((decodeSeq c).getD (m % (decodeSeq c).length) 0).unpair.2
              = m / (decodeSeq c).length then 0 else 1)
          else (if ((decodeSeq c).getD (m % (decodeSeq c).length) 0).unpair.2
              = m / (decodeSeq c).length then 1 else 0)).foldr (· + ·) 0 :=
    Primrec.list_foldr hmap (.const 0)
      ((Primrec.nat_add.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂)
  exact hfold.of_eq fun c => rfl

/-- Layer 2 helper (raw): the level-list code restricted to candidate indices
below `k` — the loop state of the pure recursion. At `k = 4 ^ n` this is the full
level code. -/
def mateLevelCodeUpTo (lt rt n k : ℕ) : ℕ :=
  seqCode (((List.range k).map fun i => seqCode (mateTable lt rt n i)).filter
    fun c => mateBadCount c = 0)

theorem mateLevelCodeUpTo_succ (lt rt n k : ℕ) :
    mateLevelCodeUpTo lt rt n (k + 1) =
      if mateBadCount (seqCode (mateTable lt rt n k)) = 0
        then seqCode (decodeSeq (mateLevelCodeUpTo lt rt n k) ++
          [seqCode (mateTable lt rt n k)])
        else mateLevelCodeUpTo lt rt n k := by
  simp only [mateLevelCodeUpTo, List.range_succ, List.map_append, List.filter_append,
    List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, decodeSeq_seqCode]
  by_cases h : mateBadCount (seqCode (mateTable lt rt n k)) = 0 <;> simp [h]

theorem seqCode_mateLevelList (lam rho : ℕ → ℕ) (n : ℕ) :
    seqCode (mateLevelList lam rho n) =
      mateLevelCodeUpTo (valueTable lam n) (valueTable rho n) n (4 ^ n) :=
  rfl

private theorem primrec_mateLevelCodeUpTo :
    Primrec fun q : ℕ => mateLevelCodeUpTo q.unpair.1 q.unpair.2.unpair.1
      q.unpair.2.unpair.2.unpair.1 q.unpair.2.unpair.2.unpair.2 := by
  have hk : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hcand : Primrec fun qy : ℕ × ℕ =>
      seqCode (mateTable qy.1.unpair.1 qy.1.unpair.2.unpair.1
        qy.1.unpair.2.unpair.2.unpair.1 qy.2) := by
    have hrepack : Primrec fun qy : ℕ × ℕ =>
        Nat.pair qy.1.unpair.1 (Nat.pair qy.1.unpair.2.unpair.1
          (Nat.pair qy.1.unpair.2.unpair.2.unpair.1 qy.2)) :=
      Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp .fst))
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
            (Primrec.unpair.comp .fst))))
          (Primrec₂.natPair.comp
            (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
              (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp .fst))))))
            .snd))
    exact (primrec_mateTableCode.comp hrepack).of_eq fun qy => by
      simp only [Nat.unpair_pair]
  have hstep : Primrec₂ fun (q : ℕ) (yIH : ℕ × ℕ) =>
      if mateBadCount (seqCode (mateTable q.unpair.1 q.unpair.2.unpair.1
          q.unpair.2.unpair.2.unpair.1 yIH.1)) = 0
        then seqCode (decodeSeq yIH.2 ++ [seqCode (mateTable q.unpair.1
          q.unpair.2.unpair.1 q.unpair.2.unpair.2.unpair.1 yIH.1)])
        else yIH.2 := by
    have hc : Primrec fun x : ℕ × (ℕ × ℕ) =>
        seqCode (mateTable x.1.unpair.1 x.1.unpair.2.unpair.1
          x.1.unpair.2.unpair.2.unpair.1 x.2.1) :=
      (hcand.comp (Primrec.pair Primrec.fst
        (Primrec.fst.comp Primrec.snd))).of_eq fun x => rfl
    have hbad : Primrec fun x : ℕ × (ℕ × ℕ) =>
        mateBadCount (seqCode (mateTable x.1.unpair.1 x.1.unpair.2.unpair.1
          x.1.unpair.2.unpair.2.unpair.1 x.2.1)) :=
      primrec_mateBadCount.comp hc
    have hIH : Primrec fun x : ℕ × (ℕ × ℕ) => x.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hsnoc : Primrec fun x : ℕ × (ℕ × ℕ) =>
        seqCode (decodeSeq x.2.2 ++ [seqCode (mateTable x.1.unpair.1
          x.1.unpair.2.unpair.1 x.1.unpair.2.unpair.2.unpair.1 x.2.1)]) :=
      Primrec₂.comp (f := fun ih x => seqCode (decodeSeq ih ++ [x]))
        primrec_snocCode'' hIH hc
    have hite : Primrec fun x : ℕ × (ℕ × ℕ) =>
        if mateBadCount (seqCode (mateTable x.1.unpair.1 x.1.unpair.2.unpair.1
            x.1.unpair.2.unpair.2.unpair.1 x.2.1)) = 0
          then seqCode (decodeSeq x.2.2 ++ [seqCode (mateTable x.1.unpair.1
            x.1.unpair.2.unpair.1 x.1.unpair.2.unpair.2.unpair.1 x.2.1)])
          else x.2.2 :=
      Primrec.ite (Primrec.eq.comp hbad (Primrec.const 0)) hsnoc hIH
    exact hite.to₂
  have hrec : ∀ lt rt n k, mateLevelCodeUpTo lt rt n k =
      Nat.rec (motive := fun _ => ℕ) (seqCode ([] : List ℕ))
        (fun y IH => if mateBadCount (seqCode (mateTable lt rt n y)) = 0
          then seqCode (decodeSeq IH ++ [seqCode (mateTable lt rt n y)])
          else IH) k := by
    intro lt rt n k
    induction k with
    | zero =>
      simp [mateLevelCodeUpTo]
    | succ y ih =>
      rw [mateLevelCodeUpTo_succ, ih]
  have h := Primrec.nat_rec' hk (Primrec.const (seqCode ([] : List ℕ))) hstep
  exact h.of_eq fun q => (hrec _ _ _ _).symm

/-- **Layer 2, `bigraphToSystem`**: the fiber graph is Turing-reducible to the
join of the two enumerator graphs. Each enumerator is consulted only through its
finite transcript (`valueTable`, along `left_le_joinSet` / `right_le_joinSet`);
the level code is a pure primitive recursion in the two transcripts. The common
edge set never enters. -/
theorem mateFiberGraph_le_join {Ω : OmegaPart} (L R : InternalFunction Ω) :
    mateFiberGraph L.eval R.eval ≤ᵀ joinSet L.graph.1 R.graph.1 := by
  classical
  have hLt : Nat.RecursiveIn {charFn (joinSet L.graph.1 R.graph.1)}
      (fun p => Part.some (valueTable L.eval p.unpair.1)) :=
    recursiveIn_comp_primrec
      (valueTable_recursiveIn (recursiveIn_of_turingReducible
        L.eval_recursiveIn_graph (left_le_joinSet _ _)))
      (Primrec.fst.comp Primrec.unpair)
  have hRt : Nat.RecursiveIn {charFn (joinSet L.graph.1 R.graph.1)}
      (fun p => Part.some (valueTable R.eval p.unpair.1)) :=
    recursiveIn_comp_primrec
      (valueTable_recursiveIn (recursiveIn_of_turingReducible
        R.eval_recursiveIn_graph (right_le_joinSet _ _)))
      (Primrec.fst.comp Primrec.unpair)
  have hpairT := recursiveIn_pair_total hLt hRt
  have hid : Nat.RecursiveIn {charFn (joinSet L.graph.1 R.graph.1)}
      fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpaired := hid.pair hpairT
  have hpost : Nat.Partrec fun m => Part.some
      (if mateLevelCodeUpTo m.unpair.2.unpair.1 m.unpair.2.unpair.2
          m.unpair.1.unpair.1 (4 ^ m.unpair.1.unpair.1) = m.unpair.1.unpair.2
        then 1 else 0) := by
    have hn : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    have hrepack : Primrec fun m : ℕ =>
        Nat.pair m.unpair.2.unpair.1 (Nat.pair m.unpair.2.unpair.2
          (Nat.pair m.unpair.1.unpair.1 (4 ^ m.unpair.1.unpair.1))) :=
      Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec₂.natPair.comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
          (Primrec₂.natPair.comp hn
            (Primrec₂.comp (f := fun (a b : ℕ) => a ^ b)
              (Primrec₂.unpaired'.mp Nat.Primrec.pow) (.const 4) hn)))
    have hlevel : Primrec fun m : ℕ =>
        mateLevelCodeUpTo m.unpair.2.unpair.1 m.unpair.2.unpair.2
          m.unpair.1.unpair.1 (4 ^ m.unpair.1.unpair.1) :=
      (primrec_mateLevelCodeUpTo.comp hrepack).of_eq fun m => by
        simp only [Nat.unpair_pair]
    have hval : Primrec fun m : ℕ =>
        if mateLevelCodeUpTo m.unpair.2.unpair.1 m.unpair.2.unpair.2
            m.unpair.1.unpair.1 (4 ^ m.unpair.1.unpair.1) = m.unpair.1.unpair.2
          then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp hlevel
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpaired).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases h : p ∈ mateFiberGraph L.eval R.eval
  · rw [if_pos (by
      rw [← seqCode_mateLevelList]
      exact (mem_mateFiberGraph_iff.mp h).symm), if_pos h]
  · rw [if_neg (fun hc => h (mem_mateFiberGraph_iff.mpr (by
      rw [seqCode_mateLevelList]
      exact hc.symm))), if_neg h]

/-! ### Layer 3: internal packaging — no graph hypotheses -/

/-- The mate-table fiber enumerator, as an internal graph-coded function —
internal by ideal closure under join of the two enumerator graphs and the
layer-2 reduction. -/
def mateFiberFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (L R : InternalFunction Ω) : InternalFunction Ω where
  graph := ⟨mateFiberGraph L.eval R.eval,
    h.mem_of_reducible (h.join L.graph.2 R.graph.2) (mateFiberGraph_le_join L R)⟩
  total := fun n => ⟨seqCode (mateLevelList L.eval R.eval n), ⟨n, rfl⟩⟩
  singleValued := fun n y y' hy hy' => by
    obtain ⟨m, hm⟩ := hy
    obtain ⟨m', hm'⟩ := hy'
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    obtain ⟨h1, rfl⟩ := Nat.pair_eq_pair.mp hm'
    rw [h1]

end ReverseMathlib.Omega
