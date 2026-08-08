/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Coding

/-!
# The structural mixed-radix enumeration (issue #39, slice 1)

`digitListOfIndex bs i` is the little-endian mixed-radix digit list of the index `i` for the
radix list `bs`. Ranging `i` below `bs.prod` enumerates every entrywise-bounded sequence
(entry `j` below radix `j`) exactly once, which is the enumeration the explicitly bounded
Kőnig compiler uses: level-`n` candidates of a bounded tree are the digit lists for the
first `n` values of the supplied bound function, filtered through the tree oracle. With
every radix equal to `2` this is exactly the role `bitListOfIndex` plays for binary trees.

The enumeration is **structural**, never a numerical scan of `seqCode` values: `seqCode` is
a bijection and carries no order property, so a search over codes would have no bound. The
laws that matter downstream are the coordinatewise bounds, injectivity below `bs.prod`,
completeness (every bounded sequence is enumerated), and the truncation normal form. Only
the enumeration direction lives here — the bounded front's decoder extracts path entries
from level nodes directly and never reads an index back from digits.
-/

namespace ReverseMathlib.Omega

/-- The little-endian mixed-radix digit list of index `i` for the radix list `bs`: the
structural enumeration of all entrywise-bounded sequences as `i` ranges below `bs.prod`. -/
def digitListOfIndex : List ℕ → ℕ → List ℕ
  | [], _ => []
  | b :: bs, i => i % b :: digitListOfIndex bs (i / b)

@[simp]
theorem digitListOfIndex_nil (i : ℕ) : digitListOfIndex [] i = [] := rfl

theorem digitListOfIndex_cons (b : ℕ) (bs : List ℕ) (i : ℕ) :
    digitListOfIndex (b :: bs) i = i % b :: digitListOfIndex bs (i / b) := rfl

@[simp]
theorem digitListOfIndex_length (bs : List ℕ) (i : ℕ) :
    (digitListOfIndex bs i).length = bs.length := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp [digitListOfIndex_cons, ih]

/-- **Coordinatewise bounds**: over positive radices, every digit is strictly below its
radix. Stated as `Forall₂` so position bookkeeping stays structural. -/
theorem digitListOfIndex_forall₂_lt {bs : List ℕ} (hpos : ∀ b ∈ bs, 0 < b) (i : ℕ) :
    List.Forall₂ (· < ·) (digitListOfIndex bs i) bs := by
  induction bs generalizing i with
  | nil => exact List.Forall₂.nil
  | cons b bs ih =>
    exact List.Forall₂.cons (Nat.mod_lt i (hpos b List.mem_cons_self))
      (ih (fun x hx => hpos x (List.mem_cons_of_mem b hx)) (i / b))

/-- The enumeration only sees the index modulo the radix product. -/
theorem digitListOfIndex_mod (bs : List ℕ) (i : ℕ) :
    digitListOfIndex bs (i % bs.prod) = digitListOfIndex bs i := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    rw [digitListOfIndex_cons, digitListOfIndex_cons, List.prod_cons,
      Nat.mod_mod_of_dvd i (dvd_mul_right b bs.prod), Nat.mod_mul_right_div_self, ih]

/-- The enumeration is injective below `bs.prod`. -/
theorem digitListOfIndex_injOn {bs : List ℕ} :
    Set.InjOn (digitListOfIndex bs) {i | i < bs.prod} := by
  induction bs with
  | nil =>
    intro i hi i' hi' _
    simp only [Set.mem_setOf_eq, List.prod_nil, Nat.lt_one_iff] at hi hi'
    omega
  | cons b bs ih =>
    intro i hi i' hi' hEq
    simp only [Set.mem_setOf_eq, List.prod_cons] at hi hi'
    rw [digitListOfIndex_cons, digitListOfIndex_cons] at hEq
    injection hEq with h1 h2
    have hdiv : i / b = i' / b :=
      ih (Set.mem_setOf_eq ▸ Nat.div_lt_of_lt_mul hi)
        (Set.mem_setOf_eq ▸ Nat.div_lt_of_lt_mul hi') h2
    calc i = b * (i / b) + i % b := (Nat.div_add_mod i b).symm
      _ = b * (i' / b) + i' % b := by rw [hdiv, h1]
      _ = i' := Nat.div_add_mod i' b

/-- **Completeness of the enumeration**: every entrywise-bounded sequence is
`digitListOfIndex` of some index below the radix product. -/
theorem exists_digitListOfIndex {l bs : List ℕ} (h : List.Forall₂ (· < ·) l bs) :
    ∃ i < bs.prod, digitListOfIndex bs i = l := by
  induction h with
  | nil => exact ⟨0, Nat.one_pos, rfl⟩
  | @cons d b l bs hdb _ ih =>
    obtain ⟨i, hi, hdi⟩ := ih
    have hb : 0 < b := by omega
    refine ⟨d + b * i, ?_, ?_⟩
    · calc d + b * i < b * i + b := by omega
        _ = b * (i + 1) := by rw [Nat.mul_succ]
        _ ≤ b * bs.prod := Nat.mul_le_mul_left b hi
        _ = (b :: bs).prod := (List.prod_cons).symm
    · rw [digitListOfIndex_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdb,
        Nat.add_mul_div_left d i hb, Nat.div_eq_of_lt hdb, Nat.zero_add, hdi]

/-- The bonding normal form: truncating an enumeration entry lands exactly on the
enumeration for the truncated radix list at the reduced index. -/
theorem digitListOfIndex_take (bs : List ℕ) (i k : ℕ) :
    (digitListOfIndex bs i).take k
      = digitListOfIndex (bs.take k) (i % (bs.take k).prod) := by
  induction bs generalizing i k with
  | nil => simp
  | cons b bs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [digitListOfIndex_cons, List.take_succ_cons, ih, List.take_succ_cons,
        List.prod_cons, digitListOfIndex_cons,
        Nat.mod_mod_of_dvd i (dvd_mul_right b (bs.take k).prod),
        Nat.mod_mul_right_div_self]

/-! ### Primitive recursiveness

The recursion consumes the radix list left to right while dividing the index down, which is
a fold with an accumulator; `Primrec.list_foldl` closes it. -/

theorem digitListOfIndex_eq_foldl (bs : List ℕ) (i : ℕ) :
    digitListOfIndex bs i
      = (bs.foldl (fun p b => (p.1 ++ [p.2 % b], p.2 / b)) (([] : List ℕ), i)).1 := by
  suffices h : ∀ (acc : List ℕ) (i : ℕ),
      (bs.foldl (fun p b => (p.1 ++ [p.2 % b], p.2 / b)) (acc, i)).1
        = acc ++ digitListOfIndex bs i by
    simpa using (h [] i).symm
  induction bs with
  | nil => simp
  | cons b bs ih =>
    intro acc i
    simp [digitListOfIndex_cons, ih]

theorem primrec_digitListOfIndex : Primrec₂ digitListOfIndex := by
  have hstep : Primrec₂ fun (_ : List ℕ × ℕ) (q : (List ℕ × ℕ) × ℕ) =>
      (q.1.1 ++ [q.1.2 % q.2], q.1.2 / q.2) :=
    ((Primrec.list_concat.comp (Primrec.fst.comp (Primrec.fst.comp .snd))
        (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.fst.comp .snd))
          (Primrec.snd.comp .snd))).pair
      (Primrec.nat_div.comp (Primrec.snd.comp (Primrec.fst.comp .snd))
        (Primrec.snd.comp .snd))).to₂
  have h : Primrec fun p : List ℕ × ℕ =>
      (p.1.foldl (fun q b => (q.1 ++ [q.2 % b], q.2 / b)) (([] : List ℕ), p.2)).1 :=
    Primrec.fst.comp (Primrec.list_foldl .fst
      ((Primrec.const ([] : List ℕ)).pair .snd) hstep)
  exact h.of_eq fun p => (digitListOfIndex_eq_foldl p.1 p.2).symm

end ReverseMathlib.Omega
