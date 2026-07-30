/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Quantitative.MonotoneSequence

/-!
# The finite convergence principle (Q4)

Kohlenbach's Corollary 2.28 and Remark 2.29 ([Koh08] pp. 31–32, PDF 48–49; SHA-256 pinned in
`Metastability.lean`): the honest finite presentation takes `a : Fin (M + 1) → ℝ` with
`M = M(g, k, C) = g̃^[C * 2 ^ k + 1] 0`, extends it constantly beyond `M`, applies the Q3
candidate theorem, and certifies that the selected challenge interval lies below `M`
(`candidate g (i + 1) ≤ M`, since the interval `[g̃^[i] 0, g̃^[i+1] 0]` is exactly one
challenge step).

The bound parameter `C` is a natural number in this pilot; general real or rational bounds
require an explicit ceiling convention and are a later theorem.
-/

namespace ReverseMathlib.Quantitative

/-- Constant extension of a finite sequence beyond its last index. -/
def extendConst {M : ℕ} (a : Fin (M + 1) → ℝ) (n : ℕ) : ℝ :=
  a ⟨min n M, Nat.lt_succ_of_le (min_le_right n M)⟩

theorem extendConst_eq_of_le {M : ℕ} (a : Fin (M + 1) → ℝ) {n : ℕ} (h : n ≤ M) :
    extendConst a n = a ⟨n, Nat.lt_succ_of_le h⟩ := by
  simp [extendConst, Nat.min_eq_left h]

theorem extendConst_antitone {M : ℕ} {a : Fin (M + 1) → ℝ} (ha : Antitone a) :
    Antitone (extendConst a) := by
  intro m n hmn
  exact ha (by simpa [Fin.mk_le_mk] using min_le_min_right M hmn)

/-- **The finite convergence principle** (Corollary 2.28 via Remark 2.29, natural `C`): a
finite antitone `[0, C]`-valued sequence of length `M(g, k, C) + 1` has a metastable candidate
whose entire challenge interval lies below `M(g, k, C)` — so only the given finite data is
ever inspected. -/
theorem finite_metastability (g : ℕ → ℕ) (k C : ℕ)
    (a : Fin (boundedFiniteHorizon g k C + 1) → ℝ)
    (hmono : Antitone a) (h0 : ∀ i, 0 ≤ a i) (hC : ∀ i, a i ≤ (C : ℝ)) :
    ∃ i ≤ C * 2 ^ k, candidate g (i + 1) ≤ boundedFiniteHorizon g k C ∧
      MetastableAt (extendConst a) k g (candidate g i) := by
  obtain ⟨i, hi, hm⟩ := exists_metastable_candidate_bounded (extendConst a) g k C
    (extendConst_antitone hmono) (fun n => h0 _) (fun n => hC _)
  exact ⟨i, hi, candidate_mono g (by omega), hm⟩

/-- The `C = 1` finite convergence principle over `M = g̃^[2 ^ k + 1] 0`. -/
theorem finite_metastability_unit (g : ℕ → ℕ) (k : ℕ)
    (a : Fin (finiteHorizon g k + 1) → ℝ)
    (hmono : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    ∃ i ≤ 2 ^ k, candidate g (i + 1) ≤ finiteHorizon g k ∧
      MetastableAt (extendConst a) k g (candidate g i) := by
  obtain ⟨i, hi, hm⟩ := exists_metastable_candidate (extendConst a) g k
    (extendConst_antitone hmono) (fun n => h0 _) (fun n => h1 _)
  exact ⟨i, hi, candidate_mono g (by omega), hm⟩

end ReverseMathlib.Quantitative
