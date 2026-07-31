/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.RecursiveIn

/-!
# Set-oracle computability substrate (issue #22, slice 1)

Set-based Turing reducibility over mathlib's oracle computability
(`Mathlib/Computability/RecursiveIn.lean`), the recursive join, and second-order parts
(`OmegaPart`) with the Turing-ideal closure conditions. This is the computability-theoretic
realization of the ω-model layer: ω-models of RCA₀ are exactly the Turing ideals.

Everything here is ambient classical mathematics about standard `ℕ`; nothing in this file is
a reverse-mathematics claim at any scope, and nothing here registers in the catalog — the
presentation-explicit statement variants and the RCAω semantic context arrive with slice 2,
and the first certified ω-scope fact only after the fact-evidence linkage (#24).

Design notes: a set is presented to the oracle machinery through its characteristic
function `charFn`, so `A ≤ᵀ B` is `Nat.RecursiveIn {charFn B} (charFn A)`. The join uses the
standard even/odd coding. The Turing jump is deliberately absent — off the critical path for
the WKLω milestone.
-/

namespace ReverseMathlib.Omega

open Classical in
/-- The characteristic partial function of a set (total, `1`/`0`-valued). Classical: the
ambient layer may decide membership; scope honesty lives in the catalog labels, not in
constructivity of the ambient definitions. -/
noncomputable def charFn (A : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (if n ∈ A then 1 else 0)

/-- Set-based Turing reducibility: the characteristic function of `A` is partial recursive
with the characteristic function of `B` as oracle. -/
def TuringReducibleSet (A B : Set ℕ) : Prop :=
  Nat.RecursiveIn {charFn B} (charFn A)

@[inherit_doc] scoped infix:50 " ≤ᵀ " => TuringReducibleSet

/-- Reducibility is reflexive: the oracle rule applied to `charFn A` itself. -/
theorem TuringReducibleSet.refl (A : Set ℕ) : A ≤ᵀ A :=
  Nat.RecursiveIn.oracle _ rfl

/-- Reducibility is transitive, by substituting the middle oracle
(`Nat.RecursiveIn.subst`). -/
theorem TuringReducibleSet.trans {A B C : Set ℕ} (hab : A ≤ᵀ B) (hbc : B ≤ᵀ C) : A ≤ᵀ C :=
  hab.subst fun _ hg => Set.mem_singleton_iff.mp hg ▸ hbc

instance : Std.Refl TuringReducibleSet := ⟨TuringReducibleSet.refl⟩

instance : Trans TuringReducibleSet TuringReducibleSet TuringReducibleSet :=
  ⟨TuringReducibleSet.trans⟩

/-- **Oracle enlargement along `≤ᵀ`**: a computation relative to `A` is a computation
relative to any oracle that computes `A`. The fundamental ω-transfer composition rule — a
construction computable from an internal graph stays computable from any larger registered
oracle. -/
theorem recursiveIn_of_turingReducible {A B : Set ℕ} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {charFn A} f) (hAB : A ≤ᵀ B) :
    Nat.RecursiveIn {charFn B} f :=
  hf.subst fun _ hg => Set.mem_singleton_iff.mp hg ▸ hAB

/-- The characteristic function determines the set. -/
theorem charFn_injective : Function.Injective charFn := by
  intro A B h
  ext n
  have hn := congrFun h n
  simp only [charFn, Part.some_inj] at hn
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [hA, hB] at hn ⊢

/-- Extensionality through the characteristic presentation. -/
theorem charFn_inj {A B : Set ℕ} : charFn A = charFn B ↔ A = B :=
  charFn_injective.eq_iff

/-- The characteristic function is total. -/
theorem charFn_dom (A : Set ℕ) (n : ℕ) : (charFn A n).Dom := trivial

/-- What the oracle answers on members. -/
theorem one_mem_charFn_iff {A : Set ℕ} {n : ℕ} : 1 ∈ charFn A n ↔ n ∈ A := by
  by_cases h : n ∈ A <;> simp [charFn, h]

/-- What the oracle answers on non-members. -/
theorem zero_mem_charFn_iff {A : Set ℕ} {n : ℕ} : 0 ∈ charFn A n ↔ n ∉ A := by
  by_cases h : n ∈ A <;> simp [charFn, h]

/-- The characteristic function is binary-valued. -/
theorem le_one_of_mem_charFn {A : Set ℕ} {n v : ℕ} (h : v ∈ charFn A n) : v ≤ 1 := by
  by_cases hA : n ∈ A <;> simp [charFn, hA] at h <;> omega

/-- The recursive join under even/odd coding: `2*a` codes membership in `A`, `2*b+1`
membership in `B`. -/
def joinSet (A B : Set ℕ) : Set ℕ :=
  {n | (n % 2 = 0 ∧ n / 2 ∈ A) ∨ (n % 2 = 1 ∧ n / 2 ∈ B)}

theorem mem_joinSet_left {A B : Set ℕ} {a : ℕ} (h : a ∈ A) : 2 * a ∈ joinSet A B :=
  Or.inl ⟨by omega, by simpa [Nat.mul_div_cancel_left] using h⟩

theorem mem_joinSet_right {A B : Set ℕ} {b : ℕ} (h : b ∈ B) : 2 * b + 1 ∈ joinSet A B :=
  Or.inr ⟨by omega, by simpa [Nat.mul_add_div] using h⟩

/-- Join normal form on the even side. -/
theorem two_mul_mem_joinSet {A B : Set ℕ} {n : ℕ} : 2 * n ∈ joinSet A B ↔ n ∈ A := by
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · simpa [Nat.mul_div_cancel_left] using h
    · omega
  · exact mem_joinSet_left

/-- Join normal form on the odd side. -/
theorem two_mul_add_one_mem_joinSet {A B : Set ℕ} {n : ℕ} :
    2 * n + 1 ∈ joinSet A B ↔ n ∈ B := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · omega
    · simpa [Nat.mul_add_div] using h
  · exact mem_joinSet_right

/-! ### Oracle computations

The construction pattern for everything below: precompose an oracle with a computable total
function (`Nat.RecursiveIn.comp`), pair streams with `Nat.RecursiveIn.pair`, and postprocess
with a primitive recursive selector. -/

/-- Precompose a relatively computable partial function with a computable total function. -/
theorem recursiveIn_comp_partrec {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn O f) {g : ℕ → ℕ} (hg : Nat.Partrec fun n => Part.some (g n)) :
    Nat.RecursiveIn O fun n => f (g n) :=
  (hf.comp hg.recursiveIn).of_eq fun n => by simp

/-! #### Total oracle-relative computations

Mathlib's `Nat.RecursiveIn` exposes only the raw constructors, so the combinators for
**total** functions — presented throughout as `fun n => Part.some (f n)` — are stated once
here rather than reproved at each use. Together with `Nat.pair` bookkeeping they are enough
to build finite oracle transcripts: query, pair, post-process, recurse. -/

/-- Primitive-recursive functions are relatively computable, for any oracle. -/
theorem recursiveIn_of_primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} (hf : Primrec f) :
    Nat.RecursiveIn O fun n => Part.some (f n) :=
  ((Nat.Partrec.of_primrec (Primrec.nat_iff.mp hf)).recursiveIn).of_eq fun _ => rfl

/-- Precompose a relatively computable partial function with a primitive-recursive one. -/
theorem recursiveIn_comp_primrec {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn O f) {g : ℕ → ℕ} (hg : Primrec g) :
    Nat.RecursiveIn O fun n => f (g n) :=
  recursiveIn_comp_partrec hf
    ((Nat.Partrec.of_primrec (Primrec.nat_iff.mp hg)).of_eq fun _ => rfl)

/-- Compose two relatively computable total functions — the outer one may query the oracle
at an argument the inner one obtained from the oracle. -/
theorem recursiveIn_comp_total {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O fun n => Part.some (f n))
    (hg : Nat.RecursiveIn O fun n => Part.some (g n)) :
    Nat.RecursiveIn O fun n => Part.some (f (g n)) :=
  (hf.comp hg).of_eq fun _ => by simp

/-- Pair two relatively computable total functions. -/
theorem recursiveIn_pair_total {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O fun n => Part.some (f n))
    (hg : Nat.RecursiveIn O fun n => Part.some (g n)) :
    Nat.RecursiveIn O fun n => Part.some (Nat.pair (f n) (g n)) :=
  (hf.pair hg).of_eq fun _ => by
    simp [Seq.seq, Part.map_eq_map, Part.bind_some, Part.map_some]

/-- **Oracle-relative primitive recursion**, with a parameter. The step function receives
the parameter, the level, and the previous value, packed as `Nat.pair a (Nat.pair y i)` —
the shape `Nat.RecursiveIn.prec` supplies. -/
theorem recursiveIn_nat_rec_param {O : Set (ℕ →. ℕ)} {base : ℕ → ℕ} {step : ℕ → ℕ → ℕ → ℕ}
    (hbase : Nat.RecursiveIn O fun a => Part.some (base a))
    (hstep : Nat.RecursiveIn O fun m =>
      Part.some (step m.unpair.1 m.unpair.2.unpair.1 m.unpair.2.unpair.2)) :
    Nat.RecursiveIn O fun p =>
      Part.some (Nat.rec (motive := fun _ => ℕ) (base p.unpair.1)
        (fun y ih => step p.unpair.1 y ih) p.unpair.2) := by
  refine (hbase.prec hstep).of_eq fun p => ?_
  obtain ⟨a, n, rfl⟩ : ∃ a n, p = Nat.pair a n :=
    ⟨p.unpair.1, p.unpair.2, (Nat.pair_unpair p).symm⟩
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.succ_eq_add_one]
    dsimp only
    rw [ih]
    simp

/-- **Oracle-relative primitive recursion**, unary. -/
theorem recursiveIn_nat_rec {O : Set (ℕ →. ℕ)} {base : ℕ} {step : ℕ → ℕ → ℕ}
    (hstep : Nat.RecursiveIn O fun m => Part.some (step m.unpair.1 m.unpair.2)) :
    Nat.RecursiveIn O fun L =>
      Part.some (Nat.rec (motive := fun _ => ℕ) base step L) := by
  have hbase : Nat.RecursiveIn O fun _ : ℕ => Part.some base :=
    recursiveIn_of_primrec (Primrec.const base)
  have hstep' : Nat.RecursiveIn O fun m =>
      Part.some (step m.unpair.2.unpair.1 m.unpair.2.unpair.2) :=
    recursiveIn_comp_primrec hstep (Primrec.snd.comp Primrec.unpair)
  have h := recursiveIn_nat_rec_param (base := fun _ => base)
    (step := fun _ y ih => step y ih) hbase hstep'
  refine (recursiveIn_comp_primrec h
    (Primrec₂.comp (f := Nat.pair) (g := fun _ : ℕ => 0) (h := fun L : ℕ => L)
      Primrec₂.natPair (Primrec.const 0) Primrec.id)).of_eq fun L => ?_
  simp only [Nat.unpair_pair]

private theorem partrec_double : Nat.Partrec fun n => Part.some (2 * n) := by
  have : Primrec fun n : ℕ => 2 * n := (Primrec.nat_mul.comp (.const 2) .id)
  exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun n => rfl

private theorem partrec_half : Nat.Partrec fun n => Part.some (n / 2) := by
  have : Primrec fun n : ℕ => n / 2 := (Primrec.nat_div.comp .id (.const 2))
  exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun n => rfl

/-- `A` reduces to the join: query the oracle at `2 * n`. -/
theorem left_le_joinSet (A B : Set ℕ) : A ≤ᵀ joinSet A B := by
  have h := recursiveIn_comp_partrec
    (Nat.RecursiveIn.oracle (O := {charFn (joinSet A B)}) _ rfl) partrec_double
  refine h.of_eq fun n => ?_
  simp only [charFn]
  by_cases hA : n ∈ A
  · rw [if_pos (mem_joinSet_left hA), if_pos hA]
  · rw [if_neg fun hc => hA (two_mul_mem_joinSet.mp hc), if_neg hA]

/-- `B` reduces to the join: query the oracle at `2 * n + 1`. -/
theorem right_le_joinSet (A B : Set ℕ) : B ≤ᵀ joinSet A B := by
  have hsucc : Nat.Partrec fun n => Part.some (2 * n + 1) := by
    have : Primrec fun n : ℕ => 2 * n + 1 :=
      Primrec.succ.comp (Primrec.nat_mul.comp (.const 2) .id)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun n => rfl
  have h := recursiveIn_comp_partrec
    (Nat.RecursiveIn.oracle (O := {charFn (joinSet A B)}) _ rfl) hsucc
  refine h.of_eq fun n => ?_
  simp only [charFn]
  by_cases hB : n ∈ B
  · rw [if_pos (mem_joinSet_right hB), if_pos hB]
  · rw [if_neg fun hc => hB (two_mul_add_one_mem_joinSet.mp hc), if_neg hB]

/-- The core join computation, uniform in the oracle set: the join's characteristic function
is computable from the two sides' characteristic functions — pair the input with both
answers at `n / 2` and select by parity. -/
private theorem charFn_joinSet_recursiveIn {O : Set (ℕ →. ℕ)} {A B : Set ℕ}
    (hA : Nat.RecursiveIn O (charFn A)) (hB : Nat.RecursiveIn O (charFn B)) :
    Nat.RecursiveIn O (charFn (joinSet A B)) := by
  have hid : Nat.RecursiveIn O fun n => Part.some n :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun n => rfl
  have hA2 := recursiveIn_comp_partrec hA partrec_half
  have hB2 := recursiveIn_comp_partrec hB partrec_half
  have ht := hid.pair (hA2.pair hB2)
  have hpost : Nat.Partrec fun m => Part.some (if (Nat.unpair m).1 % 2 = 0
      then (Nat.unpair (Nat.unpair m).2).1 else (Nat.unpair (Nat.unpair m).2).2) := by
    have hfst : Primrec fun m : ℕ => (Nat.unpair m).1 := Primrec.fst.comp Primrec.unpair
    have hsnd : Primrec fun m : ℕ => (Nat.unpair m).2 := Primrec.snd.comp Primrec.unpair
    have : Primrec fun m : ℕ => if (Nat.unpair m).1 % 2 = 0
        then (Nat.unpair (Nat.unpair m).2).1 else (Nat.unpair (Nat.unpair m).2).2 := by
      refine Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hfst (.const 2)) (.const 0))
        (Primrec.fst.comp (Primrec.unpair.comp hsnd))
        (Primrec.snd.comp (Primrec.unpair.comp hsnd))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun n => rfl
  refine (hpost.recursiveIn.comp ht).of_eq fun n => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases hpar : n % 2 = 0
  · have h2 : 2 * (n / 2) = n := by omega
    rw [if_pos hpar]
    by_cases hA' : n / 2 ∈ A
    · rw [if_pos hA', if_pos (show n ∈ joinSet A B by rw [← h2]; exact mem_joinSet_left hA')]
    · rw [if_neg hA', if_neg fun hc => hA' (two_mul_mem_joinSet.mp (by rwa [h2]))]
  · have h2 : 2 * (n / 2) + 1 = n := by omega
    rw [if_neg hpar]
    by_cases hB' : n / 2 ∈ B
    · rw [if_pos hB',
        if_pos (show n ∈ joinSet A B by rw [← h2]; exact mem_joinSet_right hB')]
    · rw [if_neg hB', if_neg fun hc => hB' (two_mul_add_one_mem_joinSet.mp (by rwa [h2]))]

/-- The join is a least upper bound for set-based Turing reducibility. -/
theorem joinSet_le {A B C : Set ℕ} (hA : A ≤ᵀ C) (hB : B ≤ᵀ C) : joinSet A B ≤ᵀ C :=
  charFn_joinSet_recursiveIn hA hB

/-- A recursive (computable) set: its characteristic function is partial recursive with no
oracle. -/
def RecursiveSet (A : Set ℕ) : Prop :=
  Nat.Partrec (charFn A)

/-- A recursive set reduces to every set. -/
theorem RecursiveSet.turingReducibleSet {A : Set ℕ} (hA : RecursiveSet A) (B : Set ℕ) :
    A ≤ᵀ B :=
  hA.recursiveIn

/-- The empty set is recursive. -/
theorem recursiveSet_empty : RecursiveSet (∅ : Set ℕ) := by
  have : Nat.Partrec fun _ : ℕ => Part.some 0 := Nat.Partrec.zero.of_eq fun n => rfl
  exact this.of_eq fun n => by simp [charFn]

/-- A second-order part: a collection of subsets of `ℕ`. An ω-structure is `(ℕ, Ω)`; the
closure conditions making it an ω-model of RCA₀ are `IsTuringIdeal`. -/
structure OmegaPart where
  /-- The second-order collection. -/
  sets : Set (Set ℕ)

/-- Membership of a set in a second-order part. -/
instance : Membership (Set ℕ) OmegaPart := ⟨fun Ω A => A ∈ Ω.sets⟩

/-- The Turing-ideal closure conditions: nonempty, downward closed under set-based Turing
reducibility, and closed under the recursive join. ω-models of RCA₀ are exactly the Turing
ideals — but *that* identification is a slice-2/backend statement; here it is only the
definition of the closure conditions. -/
structure IsTuringIdeal (Ω : OmegaPart) : Prop where
  /-- The collection is nonempty. -/
  nonempty : Ω.sets.Nonempty
  /-- Downward closure: anything reducible to a member is a member. -/
  downward : ∀ {A B : Set ℕ}, B ∈ Ω → A ≤ᵀ B → A ∈ Ω
  /-- Join closure. -/
  join : ∀ {A B : Set ℕ}, A ∈ Ω → B ∈ Ω → joinSet A B ∈ Ω

/-- The workhorse closure form for the later slices: an output computed (relative to a
member) belongs to the part. Definitionally `downward`, named for readability at use
sites. -/
theorem IsTuringIdeal.mem_of_reducible {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    {A B : Set ℕ} (hB : B ∈ Ω) (hAB : A ≤ᵀ B) : A ∈ Ω :=
  h.downward hB hAB

/-- The recursive-membership workhorse: every recursive set belongs to every Turing ideal
(nonemptiness plus downward closure) — this eliminates repetitive oracle arguments in the
internal-presentation slice. -/
theorem IsTuringIdeal.mem_of_recursive {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    {A : Set ℕ} (hA : RecursiveSet A) : A ∈ Ω := by
  obtain ⟨B, hB⟩ := h.nonempty
  exact h.downward hB (hA.turingReducibleSet B)

/-- The **recursive-set Turing ideal**: second-order part consisting of exactly the
recursive sets. Deliberately *not* yet called "an ω-model of RCA₀" — that identification
belongs to the registered RCAω context and adequacy layer (slice 2 and the backend). -/
def recursivePart : OmegaPart :=
  ⟨{A | RecursiveSet A}⟩

/-- The recursive sets form a Turing ideal. -/
theorem recursivePart_isTuringIdeal : IsTuringIdeal recursivePart where
  nonempty := ⟨∅, recursiveSet_empty⟩
  downward hB hAB :=
    Nat.RecursiveIn.partrec_of_oracle
      (fun _ hg => Set.mem_singleton_iff.mp hg ▸ hB) hAB
  join hA hB :=
    Nat.RecursiveIn.partrec_of_oracle (fun _ hg => hg.elim)
      (charFn_joinSet_recursiveIn (O := ∅) hA.recursiveIn hB.recursiveIn)

end ReverseMathlib.Omega
