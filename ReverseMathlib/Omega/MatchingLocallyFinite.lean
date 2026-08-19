/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Graph

/-!
# Locally finite marriage problems and symmetric solutions at a second-order part
(issue #51, statement layer)

The **property-shaped** presentation of Hirst's symmetric marriage theorem (thesis
Theorem 3.1): a marriage problem is one bare internal edge set over two sides of
people (an edge code `Nat.pair a b` says boy `a` knows girl `b`), with local
finiteness on **each side** as a checked existential **property** — never enumerators
or supplied bounds — and the symmetric marriage condition H_sym as a separate
cardinality-form hypothesis of the principle, exactly as `HasNodeAtEveryLevel` sits
outside `InternalFinitelyBranchingTree`. The relation itself is *not* required to be
symmetric: H_sym is the two-sided Hall condition ("every subset of n boys knows at
least n girls and every subset of n girls knows at least n boys", thesis p. 17), and
a symmetric solution is a matching that saturates both sides.

This is deliberately a **new concept**, separate from the `countableHall` family: the
audit finding is that supplying neighbor enumerators (the fact-5 presentation class)
makes the partial-solution tree's level bound computable and collapses the principle
into the supplied-bound/WKL class, while Hirst's ACA-level theorem needs local
finiteness as a bare property — the reversal gadget's neighbor enumerators are not
computable from the underlying injection. The structure therefore mirrors
`InternalFinitelyBranchingTree` (property-shaped) rather than
`InternalTwoRegularBigraph` (data-bearing), and no bridge between the two
presentation classes is claimed.

A symmetric solution is the same relational shape as the fact-5 matching: a
graph-coded internal function that is edge-respecting, injective, and surjective —
totality saturates the boys' side, surjectivity the girls'. Everything is stated
through `InternalFunction.MapsTo` and set membership; `eval` never enters a statement
(the statement-burden gate in `scripts/MetaSmoke.lean` pins this).
`LocallyFinitePerfectMatchingAt Ω` carries no base-theory premise, exactly like
`FinitelyBranchingKonigAt`.
-/

namespace ReverseMathlib.Omega

/-- An internally presented locally finite marriage problem: one bare internal edge
set (codes `Nat.pair a b` for boy `a` knows girl `b`), with local finiteness on each
side as an existential **property** — some strict bound exists on each person's
acquaintances, never supplied data ("each person knows only finitely many members of
the opposite sex"). The property-shaped ACA-level presentation (Hirst thesis §3.1),
deliberately distinct from the enumerated-neighborhood presentation class of
`InternalTwoRegularBigraph`. -/
structure InternalLocallyFiniteBigraph (Ω : OmegaPart) where
  /-- The edge set: an internal set of `Nat.pair a b` codes. -/
  edges : Ω.InternalSet
  /-- Local finiteness on the boys' side, as a property: every boy's acquaintances
  lie below some strict bound. -/
  left_locally_finite : ∀ a, ∃ k, ∀ b, Nat.pair a b ∈ edges.1 → b < k
  /-- Local finiteness on the girls' side, as a property: every girl's acquaintances
  lie below some strict bound. -/
  right_locally_finite : ∀ b, ∃ k, ∀ a, Nat.pair a b ∈ edges.1 → a < k

/-- Hirst's symmetric marriage condition H_sym, in **cardinality form**: every
duplicate-free finite list of boys has at least as many distinct joint acquaintances,
witnessed by an explicit duplicate-free list, and likewise with the sides exchanged
(thesis p. 17: "every subset of n boys knows at least n girls and every subset of n
girls knows at least n boys"). The finite SDR machinery is derived from this
separately in the forward construction, never stated here. -/
def InternalLocallyFiniteBigraph.SatisfiesSymmetricHall {Ω : OmegaPart}
    (G : InternalLocallyFiniteBigraph Ω) : Prop :=
  (∀ l : List ℕ, l.Nodup → ∃ w : List ℕ, w.Nodup ∧ l.length ≤ w.length ∧
    ∀ b ∈ w, ∃ a ∈ l, Nat.pair a b ∈ G.edges.1) ∧
  ∀ l : List ℕ, l.Nodup → ∃ w : List ℕ, w.Nodup ∧ l.length ≤ w.length ∧
    ∀ a ∈ w, ∃ b ∈ l, Nat.pair a b ∈ G.edges.1

/-- `f` is a symmetric solution of `G` — a perfect matching: a graph-coded internal
function that is edge-respecting, injective, and surjective, so with totality the
matching saturates **both** sides. Stated relationally — no selection, no `eval`. -/
def InternalLocallyFiniteBigraph.IsPerfectMatching {Ω : OmegaPart}
    (G : InternalLocallyFiniteBigraph Ω) (f : InternalFunction Ω) : Prop :=
  (∀ a b, f.MapsTo a b → Nat.pair a b ∈ G.edges.1) ∧
    (∀ a a' b, f.MapsTo a b → f.MapsTo a' b → a = a') ∧
    ∀ b, ∃ a, f.MapsTo a b

/-- Locally finite perfect matching at a second-order part: every internally
presented locally finite marriage problem satisfying the symmetric marriage condition
H_sym has an internal perfect matching (Hirst thesis Theorem 3.1's "symmetric
solution"). Local finiteness is a property, not data — the ACA-level principle,
deliberately distinct from the supplied-enumerator matching of
`TwoRegularPerfectMatchingAt`. No base-theory premise inside the capability. -/
def LocallyFinitePerfectMatchingAt (Ω : OmegaPart) : Prop :=
  ∀ G : InternalLocallyFiniteBigraph Ω, G.SatisfiesSymmetricHall →
    ∃ f : InternalFunction Ω, G.IsPerfectMatching f

end ReverseMathlib.Omega
