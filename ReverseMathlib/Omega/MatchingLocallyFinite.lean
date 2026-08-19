/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Graph

/-!
# Locally finite symmetric graphs and perfect matching at a second-order part
(issue #51, statement layer)

The **property-shaped** presentation of Hirst's symmetric marriage problem (thesis
Theorem 3.1): one bare internal edge set over a single index set of people, symmetry
and local finiteness as checked **properties** of that set — never enumerators or
supplied bounds — and the symmetric marriage condition H_sym as a separate
cardinality-form hypothesis of the principle, exactly as `HasNodeAtEveryLevel` sits
outside `InternalFinitelyBranchingTree`.

This is deliberately a **new concept**, separate from the `countableHall` family: the
audit finding is that supplying neighbor enumerators (the fact-5 presentation class)
makes the partial-solution tree's level bound computable and collapses the principle
into the supplied-bound/WKL class, while Hirst's ACA-level theorem needs local
finiteness as a bare property — the reversal gadget's neighbor enumerators are not
computable from the underlying injection. The structure therefore mirrors
`InternalFinitelyBranchingTree` (property-shaped) rather than
`InternalTwoRegularBigraph` (data-bearing), and no bridge between the two
presentation classes is claimed.

An edge code `Nat.pair a b` says person `a` knows person `b`; the `symm` field makes
the relation symmetric, so the single `locally_finite` field — every person knows
boundedly many people, an existential property — covers both roles a person can play
(the girl-side reading is the derived lemma `locally_finite_swap`, through symmetry).

A perfect matching is the same relational shape as the fact-5 matching: a graph-coded
internal function that is edge-respecting, injective, and surjective — totality
saturates one side, surjectivity the other. Everything is stated through
`InternalFunction.MapsTo` and set membership; `eval` never enters a statement (the
statement-burden gate in `scripts/MetaSmoke.lean` pins this).
`LocallyFinitePerfectMatchingAt Ω` carries no base-theory premise, exactly like
`FinitelyBranchingKonigAt`.
-/

namespace ReverseMathlib.Omega

/-- An internally presented locally finite symmetric graph: one bare internal edge set
(codes `Nat.pair a b` for person `a` adjacent to person `b`), symmetric, with local
finiteness as an existential **property** — some strict bound exists on each person's
neighbors, never supplied data. The property-shaped ACA-level presentation (Hirst
thesis §3), deliberately distinct from the enumerated-neighborhood presentation class
of `InternalTwoRegularBigraph`. -/
structure InternalLocallyFiniteSymGraph (Ω : OmegaPart) where
  /-- The edge set: an internal set of `Nat.pair a b` codes. -/
  edges : Ω.InternalSet
  /-- The relation is symmetric. -/
  symm : ∀ a b, Nat.pair a b ∈ edges.1 → Nat.pair b a ∈ edges.1
  /-- Local finiteness as a property: every person's neighbors admit some strict
  bound. By symmetry this covers both roles a person can play
  (`locally_finite_swap`). -/
  locally_finite : ∀ a, ∃ k, ∀ b, Nat.pair a b ∈ edges.1 → b < k

/-- The swapped-role reading of local finiteness, derived through symmetry: the people
who know `b` admit the same kind of bound. -/
theorem InternalLocallyFiniteSymGraph.locally_finite_swap {Ω : OmegaPart}
    (G : InternalLocallyFiniteSymGraph Ω) (b : ℕ) :
    ∃ k, ∀ a, Nat.pair a b ∈ G.edges.1 → a < k := by
  obtain ⟨k, hk⟩ := G.locally_finite b
  exact ⟨k, fun a ha => hk a (G.symm a b ha)⟩

/-- Hirst's symmetric marriage condition H_sym, in **cardinality form**: every
duplicate-free finite list of people has at least as many distinct joint neighbors,
witnessed by an explicit duplicate-free list. The finite SDR machinery is derived
from this separately in the forward construction, never stated here. -/
def InternalLocallyFiniteSymGraph.SatisfiesSymmetricHall {Ω : OmegaPart}
    (G : InternalLocallyFiniteSymGraph Ω) : Prop :=
  ∀ l : List ℕ, l.Nodup → ∃ w : List ℕ, w.Nodup ∧ l.length ≤ w.length ∧
    ∀ b ∈ w, ∃ a ∈ l, Nat.pair a b ∈ G.edges.1

/-- `f` is a perfect matching of `G`: a graph-coded internal function that is
edge-respecting, injective, and surjective — totality saturates one side of every
pair, surjectivity the other, so the matching saturates **both** sides. Stated
relationally — no selection, no `eval`. -/
def InternalLocallyFiniteSymGraph.IsPerfectMatching {Ω : OmegaPart}
    (G : InternalLocallyFiniteSymGraph Ω) (f : InternalFunction Ω) : Prop :=
  (∀ a b, f.MapsTo a b → Nat.pair a b ∈ G.edges.1) ∧
    (∀ a a' b, f.MapsTo a b → f.MapsTo a' b → a = a') ∧
    ∀ b, ∃ a, f.MapsTo a b

/-- Locally finite perfect matching at a second-order part: every internally
presented locally finite symmetric graph satisfying the symmetric marriage condition
H_sym has an internal perfect matching. Local finiteness is a property, not data —
the ACA-level principle (Hirst thesis Theorem 3.1), deliberately distinct from the
supplied-enumerator matching of `TwoRegularPerfectMatchingAt`. No base-theory premise
inside the capability. -/
def LocallyFinitePerfectMatchingAt (Ω : OmegaPart) : Prop :=
  ∀ G : InternalLocallyFiniteSymGraph Ω, G.SatisfiesSymmetricHall →
    ∃ f : InternalFunction Ω, G.IsPerfectMatching f

end ReverseMathlib.Omega
