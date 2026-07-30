/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ReverseMathlib.Quantitative.Metastability

/-!
# Metastability of bounded monotone sequences (Q3)

Kohlenbach's Proposition 2.27 ([Koh08] pp. 31–32, PDF 48–49; SHA-256 pinned in
`Metastability.lean`), in the constructive "moreover" shape first: a metastable point occurs
at one of the `2 ^ k + 1` candidates `g̃^[i] 0` with `i ≤ 2 ^ k` — exposing the finite search
space that makes the Q5 realizer almost mechanical — and the headline bounded formulation
derived from it. Remark 2.29's `[0, C]` generalization (natural `C`) is the master statement.

The endpoint-drop core is proved once, generically over a linear ordered field, so the real
metastability theorems here and the rational realizer (Q5) share one argument.

The bound `Φ(g, k) = g̃^[2 ^ k] 0` is a *metastability bound*, **not a rate of
convergence** — no computable rate exists in general.
-/

namespace ReverseMathlib.Quantitative

/-- The generic endpoint-drop core: a `[0, C]`-valued sequence cannot drop by `2⁻ᵏ` across
every one of the `C * 2 ^ k + 1` candidate challenge intervals, since the total drop would
exceed `C`. Notably antitonicity is *not* needed here — only the bounds; monotonicity enters
when localizing metastability to the endpoint condition. Proved over any linear ordered field
so the real (Q3) and rational (Q5) developments share it. -/
theorem exists_candidate_endpoint_drop_lt {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (a : ℕ → α) (g : ℕ → ℕ) (k C : ℕ)
    (h0 : ∀ n, 0 ≤ a n) (hC : ∀ n, a n ≤ C) :
    ∃ i ≤ C * 2 ^ k, a (candidate g i) - a (candidate g (i + 1)) < ((2 : α) ^ k)⁻¹ := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have key : ∀ m, m ≤ C * 2 ^ k + 1 →
      (m : α) * ((2 : α) ^ k)⁻¹ ≤ a (candidate g 0) - a (candidate g m) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hcon m (by omega)
      have hsplit : a (candidate g 0) - a (candidate g (m + 1)) =
          (a (candidate g 0) - a (candidate g m)) +
            (a (candidate g m) - a (candidate g (m + 1))) := by ring
      rw [hsplit]
      push_cast
      calc ((m : α) + 1) * ((2 : α) ^ k)⁻¹
          = (m : α) * ((2 : α) ^ k)⁻¹ + ((2 : α) ^ k)⁻¹ := by ring
        _ ≤ _ := add_le_add h1 h2
  have hfin := key (C * 2 ^ k + 1) le_rfl
  have hpow : ((2 : α) ^ k) ≠ 0 := by positivity
  have hval : ((C * 2 ^ k + 1 : ℕ) : α) * ((2 : α) ^ k)⁻¹ = (C : α) + ((2 : α) ^ k)⁻¹ := by
    push_cast
    field_simp
  have htol : (0 : α) < ((2 : α) ^ k)⁻¹ := by positivity
  have hub : a (candidate g 0) - a (candidate g (C * 2 ^ k + 1)) ≤ (C : α) := by
    have := hC (candidate g 0)
    have := h0 (candidate g (C * 2 ^ k + 1))
    linarith
  rw [hval] at hfin
  linarith

/-- Antitonicity localizes metastability to the endpoint condition: if the drop across the
inclusive challenge interval is below the tolerance, every pair inside is. -/
theorem metastableAt_of_endpoint_lt {a : ℕ → ℝ} (hmono : Antitone a) {g : ℕ → ℕ} {k n : ℕ}
    (h : a n - a (n + g n) < ((dyadic k : ℚ) : ℝ)) : MetastableAt a k g n := by
  intro i hi j hj
  rw [challengeInterval, Set.mem_Icc] at hi hj
  have hi1 := hmono hi.1
  have hi2 := hmono hi.2
  have hj1 := hmono hj.1
  have hj2 := hmono hj.2
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- **Kohlenbach Proposition 2.27 with Remark 2.29's `[0, C]` bound, candidate form** (the
book's "moreover" clause): some candidate `g̃^[i] 0` with `i ≤ C * 2 ^ k` is metastable. This
is the constructive shape — the finite search space is explicit. Not a rate of convergence. -/
theorem exists_metastable_candidate_bounded (a : ℕ → ℝ) (g : ℕ → ℕ) (k C : ℕ)
    (hmono : Antitone a) (h0 : ∀ n, 0 ≤ a n) (hC : ∀ n, a n ≤ (C : ℝ)) :
    ∃ i ≤ C * 2 ^ k, MetastableAt a k g (candidate g i) := by
  obtain ⟨i, hi, hdrop⟩ := exists_candidate_endpoint_drop_lt a g k C h0 hC
  refine ⟨i, hi, metastableAt_of_endpoint_lt hmono ?_⟩
  rw [dyadic_cast_real, ← candidate_succ]
  exact hdrop

/-- **Kohlenbach Proposition 2.27, candidate form** (`C = 1`): some candidate `g̃^[i] 0` with
`i ≤ 2 ^ k` is metastable for a `[0, 1]`-valued antitone sequence. -/
theorem exists_metastable_candidate (a : ℕ → ℝ) (g : ℕ → ℕ) (k : ℕ)
    (hmono : Antitone a) (h0 : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n ≤ 1) :
    ∃ i ≤ 2 ^ k, MetastableAt a k g (candidate g i) := by
  have h := exists_metastable_candidate_bounded a g k 1 hmono h0 (by simpa using h1)
  simpa using h

/-- **Kohlenbach Proposition 2.27, headline bounded formulation**: a metastable point occurs
at or below `Φ(g, k) = g̃^[2 ^ k] 0`. A metastability bound — not a rate of convergence. -/
theorem exists_metastable_le_bound (a : ℕ → ℝ) (g : ℕ → ℕ) (k : ℕ)
    (hmono : Antitone a) (h0 : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n ≤ 1) :
    ∃ n ≤ metastabilityBound g k, MetastableAt a k g n := by
  obtain ⟨i, hi, hm⟩ := exists_metastable_candidate a g k hmono h0 h1
  exact ⟨candidate g i, candidate_mono g hi, hm⟩

end ReverseMathlib.Quantitative
