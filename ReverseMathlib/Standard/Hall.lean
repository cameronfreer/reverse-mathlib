/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Countable Hall's theorem, standard form

The ℕ-indexed marriage theorem with explicitly finite target sets, stated over standard `ℕ` in
the `ReverseMathlib.Standard` namespace: an ambient-Lean proposition with no reverse-mathematical
semantic scope (see `ReverseMathlib.Standard.InverseLimit` for the namespace's contract).

This is the target statement of the Hall walking slice. The relative theorem
`countableHall_of_finiteInverseLimitCompactness` (`ReverseMathlib.Slice.HallFromCompactness`)
derives it from `ExplicitFiniteInverseLimitCompactness` taken as a hypothesis, replacing the
topological compactness boundary of mathlib's
`Finset.all_card_le_biUnion_card_iff_exists_injective`.

The presentation is data-bearing: the family is `t : ℕ → Finset ℕ` — each `t n` an explicitly
enumerated finite set — matching mathlib's finite Hall interface and keeping the marriage
condition checkable on explicit finite data.
-/

namespace ReverseMathlib.Standard

/-- Countable Hall: every ℕ-indexed family of explicitly finite sets satisfying the marriage
condition (every finite index set `s` has at least `s.card` combined candidates) admits an
injective transversal. -/
def CountableHall : Prop :=
  ∀ t : ℕ → Finset ℕ,
    (∀ s : Finset ℕ, s.card ≤ (s.biUnion t).card) →
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ n, f n ∈ t n

end ReverseMathlib.Standard
