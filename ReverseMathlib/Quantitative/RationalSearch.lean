/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Quantitative.MonotoneSequence

/-!
# Executable rational realizer (Q5)

The representation distinction is the point of this file:

* Proposition 2.27's *bound* works for real sequences (Q3);
* primitive-recursive **bounded search is executable for rational sequences**, because
  rational `<` is decidable;
* an exact real-number selector would require a comparison/representation oracle — that
  residual oracle is exactly what the quantitative certificate schema must eventually record.

`findMetastable` searches the candidate indices `0, …, C * 2 ^ k`, checking the endpoint
condition `a n - a (n + g n) < 2⁻ᵏ`, which suffices by antitonicity. Returning `Option ℕ` is
honest on arbitrary invalid inputs; `findMetastable_isSome` proves valid bounded input always
produces some `n` (notably needing only the bounds, not antitonicity — monotonicity enters
when interpreting the found point as genuinely metastable, `findMetastable_metastable`).

The finite-query certificate is the **locality theorem** `findMetastable_congr`: if two
sequences agree through `M(g, k, C)`, the realizer returns the same result — formalizing
"only the finite prefix is queried".
-/

namespace ReverseMathlib.Quantitative

/-- Executable bounded search over the candidates `g̃^[i] 0`, `i ≤ C * 2 ^ k`: return the
first candidate whose inclusive challenge interval has endpoint drop strictly below `2⁻ᵏ`.
Decidable because the sequence is rational. -/
def findMetastable (a : ℕ → ℚ) (g : ℕ → ℕ) (k C : ℕ) : Option ℕ :=
  ((List.range (C * 2 ^ k + 1)).map (candidate g)).find? fun n =>
    decide (a n - a (n + g n) < dyadic k)

/-- Totality on valid input: bounds alone guarantee the search succeeds (the generic
endpoint-drop core needs no antitonicity). -/
theorem findMetastable_isSome (a : ℕ → ℚ) (g : ℕ → ℕ) (k C : ℕ)
    (h0 : ∀ n, 0 ≤ a n) (hC : ∀ n, a n ≤ (C : ℚ)) :
    (findMetastable a g k C).isSome := by
  obtain ⟨i, hi, hdrop⟩ := exists_candidate_endpoint_drop_lt a g k C h0 hC
  rw [findMetastable, List.find?_isSome]
  refine ⟨candidate g i, List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
  rw [decide_eq_true_eq, ← candidate_succ]
  exact hdrop

/-- What a successful search certifies: the endpoint condition at the returned point, which
is one of the candidates. -/
theorem findMetastable_spec {a : ℕ → ℚ} {g : ℕ → ℕ} {k C n : ℕ}
    (h : findMetastable a g k C = some n) :
    a n - a (n + g n) < dyadic k ∧ ∃ i ≤ C * 2 ^ k, n = candidate g i := by
  refine ⟨by simpa using List.find?_some h, ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some h)
  exact ⟨i, Nat.lt_succ_iff.mp (List.mem_range.mp hi), rfl⟩

/-- With antitonicity, the found point is genuinely metastable (for the real-valued cast of
the sequence). -/
theorem findMetastable_metastable {a : ℕ → ℚ} {g : ℕ → ℕ} {k C n : ℕ}
    (hmono : Antitone a) (h : findMetastable a g k C = some n) :
    MetastableAt (fun m => ((a m : ℚ) : ℝ)) k g n := by
  have h1 := (findMetastable_spec h).1
  apply metastableAt_of_endpoint_lt (fun x y hxy => by exact_mod_cast hmono hxy)
  exact_mod_cast h1

private theorem find?_congr {α : Type*} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have hx : p x = q x := h x List.mem_cons_self
    rw [List.find?_cons, List.find?_cons, hx]
    cases q x
    · exact ih fun y hy => h y (List.mem_cons_of_mem x hy)
    · rfl

/-- **The finite-query certificate (locality)**: if two sequences agree through
`M(g, k, C) = g̃^[C * 2 ^ k + 1] 0`, the realizer returns the same result — only the finite
prefix is ever queried. -/
theorem findMetastable_congr {a b : ℕ → ℚ} {g : ℕ → ℕ} {k C : ℕ}
    (hagree : ∀ n ≤ boundedFiniteHorizon g k C, a n = b n) :
    findMetastable a g k C = findMetastable b g k C := by
  unfold findMetastable
  apply find?_congr
  intro n hn
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
  have hi' : i ≤ C * 2 ^ k := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
  have h1 : candidate g i ≤ boundedFiniteHorizon g k C := candidate_mono g (by omega)
  have h2 : candidate g i + g (candidate g i) ≤ boundedFiniteHorizon g k C := by
    rw [← candidate_succ]
    exact candidate_mono g (by omega)
  rw [hagree _ h1, hagree _ h2]

/-! ## Evaluated examples -/

-- The constant sequence is metastable at the first candidate.
set_option linter.hashCommand false in
/-- info: some 0 -/
#guard_msgs in
#eval findMetastable (fun _ => 0) (fun _ => 1) 3 1

-- `a n = 1 / (n + 1)`, challenge `g = 1`, tolerance `2⁻¹`: the drop at candidate 0 is
-- exactly `1/2`, which fails the strict inequality; candidate 1 succeeds.
set_option linter.hashCommand false in
/-- info: some 1 -/
#guard_msgs in
#eval findMetastable (fun n => 1 / ((n : ℚ) + 1)) (fun _ => 1) 1 1

end ReverseMathlib.Quantitative
