/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Coding

/-!
# The structural bit-vector enumeration (issue #22, slice 3)

`bitListOfIndex n i` is the length-`n` bit list of the index `i`. Ranging `i` below `2 ^ n`
enumerates every length-`n` bit vector exactly once, which is the enumeration both bridge
directions use: `treeToSystem` filters the enumerated codes through the tree oracle, and
`systemToTree` writes chunk indices as bit blocks.

The enumeration is **structural**, never a numerical scan of `seqCode` values: `seqCode` is
a bijection and carries no order property, so a search over codes would have no bound. The
three laws that matter downstream are injectivity below `2 ^ n`, completeness (every bit
list is enumerated), and the truncation normal form.
-/

namespace ReverseMathlib.Omega

/-- The length-`n` bit list of index `i` (bit `j` of `i`, little-endian): the structural
enumeration of all length-`n` bit vectors as `i` ranges below `2 ^ n`. -/
def bitListOfIndex (n i : ℕ) : List ℕ :=
  (List.range n).map fun j => if i.testBit j then 1 else 0

@[simp]
theorem bitListOfIndex_length (n i : ℕ) : (bitListOfIndex n i).length = n := by
  simp [bitListOfIndex]

theorem isBitSeqCode_seqCode_bitListOfIndex (n i : ℕ) :
    IsBitSeqCode (seqCode (bitListOfIndex n i)) := by
  intro x hx
  rw [decodeSeq_seqCode] at hx
  simp only [bitListOfIndex, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  split <;> omega

/-- The structural candidate enumeration, arithmetically: bit `j` of `i` is
`i / 2 ^ j % 2`. -/
theorem bitListOfIndex_eq_div_mod (n i : ℕ) :
    bitListOfIndex n i = (List.range n).map fun j => i / 2 ^ j % 2 := by
  unfold bitListOfIndex
  refine List.map_congr_left fun j _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with h | h <;>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, h]

/-- The enumeration is injective below `2 ^ n`. -/
theorem bitListOfIndex_injOn {n : ℕ} :
    Set.InjOn (bitListOfIndex n) {i | i < 2 ^ n} := by
  intro i hi i' hi' hEq
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < n
  · have h1 := congrArg (fun l => l[j]?) hEq
    simp only [bitListOfIndex, List.getElem?_map, List.getElem?_range, hj] at h1
    rcases hti : i.testBit j <;> rcases hti' : i'.testBit j <;> simp_all
  · have hb : ∀ m : ℕ, m < 2 ^ n → m.testBit j = false := fun m hm => by
      have hmj : m < 2 ^ j :=
        lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (le_of_not_gt hj))
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hmj]
    rw [hb i hi, hb i' hi']

/-- **Completeness of the enumeration**: every bit list is `bitListOfIndex` of some index
below `2 ^ length`. -/
theorem exists_bitListOfIndex :
    ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 1) →
      ∃ i < 2 ^ l.length, bitListOfIndex l.length i = l := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, Nat.one_pos, rfl⟩
  | cons b t ih =>
    intro hbits
    obtain ⟨i, hi, hbi⟩ := ih fun x hx => hbits x (List.mem_cons_of_mem b hx)
    have hb : b ≤ 1 := hbits b List.mem_cons_self
    refine ⟨b + 2 * i, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      omega
    · have hcons : bitListOfIndex (t.length + 1) (b + 2 * i) =
          b :: bitListOfIndex t.length i := by
        unfold bitListOfIndex
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        · have hb2 : (b + 2 * i) % 2 = b := by omega
          rcases show b = 0 ∨ b = 1 by omega with rfl | rfl <;>
            simp [Nat.testBit_zero, hb2]
        · refine List.map_congr_left fun j _ => ?_
          have h2 : (b + 2 * i) / 2 = i := by omega
          simp [Function.comp, Nat.testBit_succ, h2]
      rw [show (b :: t).length = t.length + 1 from rfl, hcons, hbi]

/-- The head normal form of the enumeration: the first bit is the parity, and the tail
enumerates the halved index. -/
theorem bitListOfIndex_succ (n i : ℕ) :
    bitListOfIndex (n + 1) i = i % 2 :: bitListOfIndex n (i / 2) := by
  unfold bitListOfIndex
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [Nat.testBit_zero, h]
  · refine List.map_congr_left fun j _ => ?_
    simp [Function.comp, Nat.testBit_succ]

/-- The bonding normal form: truncating a level-`n + 1` enumeration entry lands exactly on
the level-`n` enumeration at the reduced index. -/
theorem bitListOfIndex_take (n i : ℕ) :
    (bitListOfIndex (n + 1) i).take n = bitListOfIndex n (i % 2 ^ n) := by
  rw [bitListOfIndex_eq_div_mod, bitListOfIndex_eq_div_mod, ← List.map_take,
    List.take_range, show min n (n + 1) = n by omega]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  have hsplit : 2 ^ n = 2 ^ j * 2 ^ (n - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : n - j ≠ 0))]

/-! ### Decoding the enumeration

`natOfBits` reads a little-endian bit list back to an index. It is total on every list of
naturals; on genuine enumeration entries it is the exact inverse modulo `2 ^ length`
(`natOfBits_bitListOfIndex`), which is what the path decoder uses to recover a chunk's
fiber index from raw bits. -/

/-- Read a little-endian bit list back to the index it enumerates. Total on any list. -/
def natOfBits : List ℕ → ℕ
  | [] => 0
  | b :: t => b + 2 * natOfBits t

theorem natOfBits_nil : natOfBits [] = 0 := rfl

theorem natOfBits_cons (b : ℕ) (t : List ℕ) : natOfBits (b :: t) = b + 2 * natOfBits t :=
  rfl

theorem natOfBits_eq_foldr (l : List ℕ) :
    natOfBits l = l.foldr (fun b acc => b + 2 * acc) 0 := by
  induction l with
  | nil => rfl
  | cons b t ih => rw [natOfBits_cons, List.foldr_cons, ih]

/-- **The enumeration decodes**: reading back the bit list of `i` recovers `i` modulo
`2 ^ n` — in particular exactly `i` whenever `i < 2 ^ n`. -/
theorem natOfBits_bitListOfIndex (n i : ℕ) : natOfBits (bitListOfIndex n i) = i % 2 ^ n := by
  induction n generalizing i with
  | zero => simp [bitListOfIndex, natOfBits, Nat.mod_one]
  | succ n ih =>
    rw [bitListOfIndex_succ, natOfBits_cons, ih, pow_succ, mul_comm (2 ^ n) 2, Nat.mod_mul]

/-! ### Primitive recursiveness -/

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_natOfBits : Primrec natOfBits := by
  have h : Primrec fun l : List ℕ => l.foldr (fun b acc => b + 2 * acc) 0 :=
    Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ : List ℕ => (0 : ℕ))
      (h := fun (_ : List ℕ) (p : ℕ × ℕ) => p.1 + 2 * p.2)
      Primrec.id (Primrec.const 0)
      ((Primrec.nat_add.comp (Primrec.fst.comp .snd)
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp .snd))).to₂)
  exact h.of_eq fun l => (natOfBits_eq_foldr l).symm

theorem primrec_bitListOfIndex : Primrec₂ bitListOfIndex := by
  have h : Primrec fun p : ℕ × ℕ => (List.range p.1).map fun j => p.2 / 2 ^ j % 2 :=
    Primrec.list_map (Primrec.list_range.comp .fst)
      (Primrec.nat_mod.comp
        (Primrec.nat_div.comp (Primrec.snd.comp .fst)
          (Primrec₂.comp primrec_natPow (Primrec.const 2) .snd))
        (Primrec.const 2)).to₂
  exact h.of_eq fun p => (bitListOfIndex_eq_div_mod p.1 p.2).symm

end ReverseMathlib.Omega
