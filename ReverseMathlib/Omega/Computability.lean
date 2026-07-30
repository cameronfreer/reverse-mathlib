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

/-- The recursive join under even/odd coding: `2*a` codes membership in `A`, `2*b+1`
membership in `B`. -/
def joinSet (A B : Set ℕ) : Set ℕ :=
  {n | (n % 2 = 0 ∧ n / 2 ∈ A) ∨ (n % 2 = 1 ∧ n / 2 ∈ B)}

theorem mem_joinSet_left {A B : Set ℕ} {a : ℕ} (h : a ∈ A) : 2 * a ∈ joinSet A B :=
  Or.inl ⟨by omega, by simpa [Nat.mul_div_cancel_left] using h⟩

theorem mem_joinSet_right {A B : Set ℕ} {b : ℕ} (h : b ∈ B) : 2 * b + 1 ∈ joinSet A B :=
  Or.inr ⟨by omega, by simpa [Nat.mul_add_div] using h⟩

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

end ReverseMathlib.Omega
