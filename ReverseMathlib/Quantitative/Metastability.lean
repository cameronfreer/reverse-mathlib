/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# Metastability vocabulary (Q2)

The quantitative spine of the Q-track pilot, following Kohlenbach's analysis of bounded
monotone sequences.

Source pin: [Koh08] Ulrich Kohlenbach, *Applied Proof Theory*, Springer 2008 — Proposition
2.27 and Corollary 2.28, printed pp. 31–32 (PDF pages 48–49);
SHA-256 `027d72cfa73b86616e85fa19a35ad10ffa7248eae13b364aa29a590933b81b45`.

Off-by-one conventions, each pinned by an `example` below because each is an easy error
source:

* the challenge interval `[n, n + g n]` is **inclusive**;
* `g̃ n = n + g n`, **not** `n + g n + 1`;
* the metastability conclusion uses **strict** `< 2⁻ᵏ`;
* the candidate index satisfies `i ≤ 2 ^ k`, giving `2 ^ k + 1` candidates;
* `Φ(g, k) = g̃^[2 ^ k] 0`;
* the finite horizon is `g̃^[2 ^ k + 1] 0`, **not** `Φ(g, k) + 1`.

The shared dyadic tolerance is a single rational definition, so the real and rational
developments cannot drift through coercions. This module is ordinary mathematics: it imports
no registry machinery, and nothing here is a catalog fact.
-/

namespace ReverseMathlib.Quantitative

/-- The challenge step `g̃ n = n + g n` (not `n + g n + 1`). -/
def challengeStep (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  n + g n

/-- The `i`-th candidate start point: `g̃^[i] 0`. -/
def candidate (g : ℕ → ℕ) (i : ℕ) : ℕ :=
  (challengeStep g)^[i] 0

/-- Kohlenbach's uniform metastability bound `Φ(g, k) = g̃^[2 ^ k] 0`. -/
def metastabilityBound (g : ℕ → ℕ) (k : ℕ) : ℕ :=
  candidate g (2 ^ k)

/-- The finite horizon `g̃^[2 ^ k + 1] 0` (Corollary 2.28's `M`) — one more challenge step
past the bound, **not** `Φ(g, k) + 1`. -/
def finiteHorizon (g : ℕ → ℕ) (k : ℕ) : ℕ :=
  candidate g (2 ^ k + 1)

/-- The `[0, C]`-bounded metastability bound `Φ(g, k, C) = g̃^[C * 2 ^ k] 0`
(Remark 2.29). -/
def boundedMetastabilityBound (g : ℕ → ℕ) (k C : ℕ) : ℕ :=
  candidate g (C * 2 ^ k)

/-- The `[0, C]`-bounded finite horizon `M(g, k, C) = g̃^[C * 2 ^ k + 1] 0`. -/
def boundedFiniteHorizon (g : ℕ → ℕ) (k C : ℕ) : ℕ :=
  candidate g (C * 2 ^ k + 1)

/-- The shared dyadic tolerance `2⁻ᵏ`, defined once over `ℚ` so the real and rational
developments agree by coercion rather than by parallel definitions. -/
def dyadic (k : ℕ) : ℚ :=
  (2 ^ k)⁻¹

/-- The inclusive challenge interval `[n, n + g n]`. -/
def challengeInterval (g : ℕ → ℕ) (n : ℕ) : Set ℕ :=
  Set.Icc n (n + g n)

/-- Metastability at `n` for challenge `g` and tolerance `2⁻ᵏ`: every two indices in the
inclusive challenge interval have values strictly within `2⁻ᵏ`. -/
def MetastableAt (a : ℕ → ℝ) (k : ℕ) (g : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i ∈ challengeInterval g n, ∀ j ∈ challengeInterval g n,
    |a i - a j| < ((dyadic k : ℚ) : ℝ)

/-! ## Convention pins (each an off-by-one source) -/

example (g : ℕ → ℕ) (n : ℕ) : challengeStep g n = n + g n := rfl

-- the interval is inclusive at both ends
example (g : ℕ → ℕ) (n : ℕ) : n ∈ challengeInterval g n :=
  Set.left_mem_Icc.mpr (Nat.le_add_right _ _)
example (g : ℕ → ℕ) (n : ℕ) : n + g n ∈ challengeInterval g n :=
  Set.right_mem_Icc.mpr (Nat.le_add_right _ _)

example (g : ℕ → ℕ) (k : ℕ) : metastabilityBound g k = candidate g (2 ^ k) := rfl
example (g : ℕ → ℕ) (k : ℕ) : finiteHorizon g k = candidate g (2 ^ k + 1) := rfl
example (g : ℕ → ℕ) (k : ℕ) : boundedMetastabilityBound g k 1 = metastabilityBound g k := by
  simp [boundedMetastabilityBound, metastabilityBound]
example (g : ℕ → ℕ) (k : ℕ) : boundedFiniteHorizon g k 1 = finiteHorizon g k := by
  simp [boundedFiniteHorizon, finiteHorizon]

/-! ## Basic candidate arithmetic -/

@[simp]
theorem candidate_zero (g : ℕ → ℕ) : candidate g 0 = 0 := rfl

theorem candidate_succ (g : ℕ → ℕ) (i : ℕ) :
    candidate g (i + 1) = candidate g i + g (candidate g i) :=
  Function.iterate_succ_apply' (challengeStep g) i 0

theorem le_candidate_succ (g : ℕ → ℕ) (i : ℕ) : candidate g i ≤ candidate g (i + 1) := by
  rw [candidate_succ]
  exact Nat.le_add_right _ _

theorem candidate_mono (g : ℕ → ℕ) : Monotone (candidate g) :=
  monotone_nat_of_le_succ (le_candidate_succ g)

theorem dyadic_pos (k : ℕ) : 0 < dyadic k :=
  inv_pos.mpr (pow_pos (by norm_num) k)

@[simp]
theorem dyadic_cast_real (k : ℕ) : ((dyadic k : ℚ) : ℝ) = ((2 : ℝ) ^ k)⁻¹ := by
  simp [dyadic]

end ReverseMathlib.Quantitative
