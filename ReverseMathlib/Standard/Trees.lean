/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.GetD
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

/-- A path proposition determines nodes: two bit lists of equal length whose entries both match
`p` are equal. This is the unique-choice boundary of the ambient path representation — a path
determines at most one node of each length. -/
theorem eq_of_matches_path {p : Set ℕ} {l l' : List Bool} (hlen : l.length = l'.length)
    (h : ∀ i, (hi : i < l.length) → (l[i] = true ↔ i ∈ p))
    (h' : ∀ i, (hi : i < l'.length) → (l'[i] = true ↔ i ∈ p)) : l = l' := by
  apply List.ext_getElem hlen
  intro i hi hi'
  have hiff := (h i hi).trans ((h' i hi').symm)
  cases hb : l[i] <;> cases hb' : l'[i] <;> simp_all

/-- Through a path there is exactly one matching node of each length. Note the caveat: ambient
proofs may *select* these uniquely determined nodes inside a `Prop` proof (via choice), which
is not yet an extracted path-decoding program — that distinction is the quantitative track's
business. -/
theorem IsBinaryPathThrough.existsUnique_node {p : Set ℕ} {T : Set (List Bool)}
    (hp : IsBinaryPathThrough p T) (n : ℕ) :
    ∃! l : List Bool, l ∈ T ∧ l.length = n ∧ ∀ i, (hi : i < l.length) → (l[i] = true ↔ i ∈ p) := by
  obtain ⟨l, hlT, hlen, hmatch⟩ := hp n
  refine ⟨l, ⟨hlT, hlen, hmatch⟩, ?_⟩
  rintro l' ⟨-, hlen', hmatch'⟩
  exact eq_of_matches_path (by omega) hmatch' hmatch

/-- A coherent chain of tree nodes — one node of each length, each truncating to the previous —
assembles into a path: the set of positions where the chain's bits are `true`. The chain itself
supplies the witnesses, so no tree structure is needed beyond membership of the chain. -/
theorem exists_path_of_coherent_chain {T : Set (List Bool)} (L : ℕ → List Bool)
    (hmem : ∀ n, L n ∈ T) (hlen : ∀ n, (L n).length = n)
    (htake : ∀ n, (L (n + 1)).take n = L n) : ∃ p : Set ℕ, IsBinaryPathThrough p T := by
  have hLprefix : ∀ {n m : ℕ}, n ≤ m → (L m).take n = L n := by
    intro n m hnm
    induction m with
    | zero =>
      have : n = 0 := by omega
      subst this
      simp [List.take_of_length_le (by rw [hlen])]
    | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h | h
      · have hnm' : n ≤ m := by omega
        rw [← ih hnm', ← htake m, List.take_take, Nat.min_eq_left hnm']
      · have : n = m + 1 := by omega
        subst this
        exact List.take_of_length_le (by rw [hlen])
  have hget : ∀ {n m i : ℕ} (hnm : n ≤ m) (hi : i < n),
      (L m)[i]'(by rw [hlen]; omega) = (L n)[i]'(by rw [hlen]; omega) := by
    intro n m i hnm hi
    have hw : i < ((L m).take n).length := by
      rw [List.length_take, hlen]
      omega
    calc (L m)[i]'(by rw [hlen]; omega)
        = ((L m).take n)[i]'hw := (List.getElem_take (h := hw)).symm
      _ = (L n)[i]'(by rw [hlen]; omega) := by
          have := List.getElem_of_eq (hLprefix hnm) hw
          simpa using this
  refine ⟨{k | (L (k + 1)).getD k false = true}, ?_⟩
  intro n
  refine ⟨L n, hmem n, hlen n, ?_⟩
  intro i hi
  have hi' : i < n := by rwa [hlen n] at hi
  have h1 : (L n)[i]'hi = (L (i + 1))[i]'(by rw [hlen]; omega) := hget (by omega) (by omega)
  have h2 : (L (i + 1)).getD i false = (L (i + 1))[i]'(by rw [hlen]; omega) :=
    List.getD_eq_getElem _ _ _
  constructor
  · intro h
    change (L (i + 1)).getD i false = true
    rw [h2, ← h1, h]
  · intro h
    have h3 : (L (i + 1)).getD i false = true := h
    rw [h2] at h3
    rw [h1, h3]

end ReverseMathlib.Standard
