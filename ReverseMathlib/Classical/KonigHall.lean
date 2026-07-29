/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.KonigLemma
import ReverseMathlib.Slice.HallFromCompactness
import ReverseMathlib.Slice.WeakKonigEfilc

/-!
# Classical instances: the end-to-end König–Hall chain

The ambient principles proved outright, **in a separate file from the relative proofs** so
factorization audits stay clean, composed explicitly through the walking slices:

```
mathlib Kőnig lemma (exists_seq_forall_proj_of_forall_finite)
        ↓
Classical.weakKonig
        ↓ Slice.efilc_of_weakKonig
Classical.explicitFiniteInverseLimitCompactness
        ↓ Slice.countableHall_of_finiteInverseLimitCompactness
Classical.countableHall
        ↓
Classical.countableHall_nat
```

Only `weakKonig` is proved directly (from mathlib's order-theoretic Kőnig lemma — not the
topological/categorical route); everything below it is derived through the existing relative
theorems, by explicit theorem constants rather than hidden instances, so the dependency gates
in `scripts/MetaSmoke.lean` can certify the chain's exact shape: `countableHall_nat` reaches
both relative bridges and finite Hall, and never mathlib's infinite Hall theorem or the
topological inverse-limit theorem.

These are classical wrappers over standard ℕ. They carry no reverse-mathematical content
themselves — the honest artifacts remain the factorizations they compose.
-/

assert_not_exists nonempty_sections_of_finite_inverse_system
assert_not_exists Finset.all_card_le_biUnion_card_iff_exists_injective

namespace ReverseMathlib.Classical

open ReverseMathlib.Standard

/-- Weak Kőnig's lemma holds outright in ambient Lean, via mathlib's order-theoretic Kőnig
lemma applied to the levels of the tree. -/
theorem weakKonig : WeakKonig := by
  intro T hT hlev
  let α : ℕ → Type := fun i => {l : List Bool // l ∈ T ∧ l.length = i}
  have hfinite : ∀ i, Finite (α i) := by
    intro i
    apply Finite.of_injective (fun l : α i => fun j : Fin i => l.val[j]'(by
      rw [l.property.2]
      exact j.isLt))
    intro ⟨l, hl, hlen⟩ ⟨l', hl', hlen'⟩ h
    apply Subtype.ext
    change l = l'
    apply List.ext_getElem (by omega)
    intro j hj hj'
    exact congrFun h ⟨j, by omega⟩
  have hnonempty : ∀ i, Nonempty (α i) := by
    intro i
    obtain ⟨l, hl, hlen⟩ := hlev i
    exact ⟨⟨l, hl, hlen⟩⟩
  have := hfinite 0
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (α := α)
    (fun {i j} hij l => ⟨l.val.take i, hT.take_mem l.property.1 i, by
      rw [List.length_take, l.property.2]
      omega⟩)
    (fun i a => Subtype.ext (List.take_of_length_le (le_of_eq a.property.2)))
    (fun i j k hij hjk a => Subtype.ext (by
      change (a.val.take j).take i = a.val.take i
      rw [List.take_take, Nat.min_eq_left hij]))
    (fun i a => Set.toFinite _)
  exact exists_path_of_coherent_chain (fun n => (f n).val)
    (fun n => (f n).property.1) (fun n => (f n).property.2)
    (fun n => congrArg Subtype.val (hf (Nat.le_add_right n 1)))

/-- Explicit finite inverse-limit compactness, derived through the relative bridge — not
independently reproved. -/
theorem explicitFiniteInverseLimitCompactness : ExplicitFiniteInverseLimitCompactness :=
  Slice.efilc_of_weakKonig weakKonig

/-- Countable Hall, derived through the relative Hall theorem. -/
theorem countableHall : CountableHall :=
  Slice.countableHall_of_finiteInverseLimitCompactness explicitFiniteInverseLimitCompactness

/-- The pleasant ℕ-facing corollary: every ℕ-indexed family of finite sets satisfying the
marriage condition admits an injective transversal. The end of the end-to-end chain. -/
theorem countableHall_nat (t : ℕ → Finset ℕ)
    (ht : ∀ s : Finset ℕ, s.card ≤ (s.biUnion t).card) :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ n, f n ∈ t n :=
  countableHall t ht

end ReverseMathlib.Classical
