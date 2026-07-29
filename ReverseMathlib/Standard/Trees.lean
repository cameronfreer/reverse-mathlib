/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.Induction
import Mathlib.Data.Set.Finite.Basic

/-!
# Coded trees, ambient list-based surface

Tree presentations for the walking slice, kept **deliberately distinct** — these formulations
have different reverse-mathematical behavior and must never collapse into one notion:

* binary trees: prefix-closed `Set (List Bool)`;
* explicitly bounded trees: prefix-closed `Set (List ℕ)` with a *supplied* coordinatewise bound;
* merely finitely branching trees: prefix-closed `Set (List ℕ)` with a finite-successor
  proposition and no supplied bound.

Representation contract (ROADMAP tranche 1, item 5): ordinary finite lists at the mathematical
surface; encoding into naturals happens only inside bridges that need it (e.g. the EFILC
bridge), so mathlib's `Encodable` representation is not prematurely blessed as the eventual
RCA₀ coding. Canonical numeric and internal (ω-model) adapters are tranche 3.

Paths: a binary ambient path is a `Set ℕ`, interpreted as the set of positions containing `1`
(matching the future internal-set representation); `IsBinaryPathThrough` matches the path
against tree nodes existentially, so no decidability of membership is assumed. A future ω-model
path will be an internal graph set with totality and single-valuedness proofs.

Everything here is an **ambient-Lean** statement in the `ReverseMathlib.Standard` namespace:
provable outright in Lean, carrying no reverse-mathematical semantic scope, serving as named
hypotheses for relative theorems (see `ReverseMathlib.Standard.InverseLimit` for the
namespace's contract).
-/

namespace ReverseMathlib.Standard

/-- A tree on `α`: a set of finite sequences closed under removing the last entry. Iterating
gives closure under arbitrary truncation, so no further conditions are needed. -/
def IsTree {α : Type*} (T : Set (List α)) : Prop :=
  ∀ ⦃l : List α⦄ ⦃a : α⦄, l ++ [a] ∈ T → l ∈ T

/-- The tree has a node of every length. For finitely branching trees this is the honest
replacement for an ambiguous "`T` is infinite". -/
def HasNodeAtEveryLevel {α : Type*} (T : Set (List α)) : Prop :=
  ∀ n : ℕ, ∃ l ∈ T, l.length = n

/-- Entries at depth `i` are bounded by the *supplied* bound `b i`. An explicitly bounded tree
is a tree of naturals together with such a bound — supplied data, not a mere existence
statement, because the difference is reverse-mathematically significant. -/
def EntriesBounded (T : Set (List ℕ)) (b : ℕ → ℕ) : Prop :=
  ∀ l ∈ T, ∀ i, (hi : i < l.length) → l[i] < b i

/-- Merely finitely branching: every node has finitely many one-step extensions, with no
supplied bound. Kept distinct from `EntriesBounded` on purpose: over a weak base the two
diverge (bounded König stays at WKL₀-level, unrestricted finitely-branching König is
ACA₀-level). -/
def IsFinitelyBranching (T : Set (List ℕ)) : Prop :=
  ∀ l ∈ T, {a : ℕ | l ++ [a] ∈ T}.Finite

/-- `p : Set ℕ` is a path through the binary tree `T`, reading `p` as the set of positions
containing `1`: at every length there is a node of `T` agreeing with `p`. Existential matching
avoids assuming membership in `p` is decidable. -/
def IsBinaryPathThrough (p : Set ℕ) (T : Set (List Bool)) : Prop :=
  ∀ n : ℕ, ∃ l ∈ T, l.length = n ∧ ∀ i, (hi : i < l.length) → (l[i] = true ↔ i ∈ p)

/-- Weak Kőnig's lemma, ambient form: every binary tree with a node at every level has a path
(a `Set ℕ` of positions). Provable outright in Lean; its role is to be taken as a hypothesis by
relative theorems whose proof terms visibly factor through it. -/
def WeakKonig : Prop :=
  ∀ T : Set (List Bool), IsTree T → HasNodeAtEveryLevel T → ∃ p : Set ℕ, IsBinaryPathThrough p T

/-! Basic closure lemmas, usable by any bridge. -/

/-- Trees are closed under truncation. -/
theorem IsTree.take_mem {α : Type*} {T : Set (List α)} (hT : IsTree T) {l : List α}
    (hl : l ∈ T) (n : ℕ) : l.take n ∈ T := by
  induction l using List.reverseRecOn with
  | nil => simpa using hl
  | append_singleton l a ih =>
    rcases Nat.lt_or_ge n (l ++ [a]).length with h | h
    · have hlen : n ≤ l.length := by
        simp only [List.length_append, List.length_singleton] at h
        omega
      rw [List.take_append_of_le_length hlen]
      exact ih (hT hl)
    · simpa [List.take_of_length_le h] using hl

end ReverseMathlib.Standard
