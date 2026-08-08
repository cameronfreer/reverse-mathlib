/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Graph
import ReverseMathlib.Omega.InternalSet

/-!
# The bridge-local disjoint-range separation interface (issue #42, slice 3)

The internal form of Hirst's Theorem 1.2 (ii) (thesis p. 7; the WKL₀
characterization Shafer's Theorem 6.1.2 reversal targets): if `f` and `g` are
**injections** with disjoint ranges, there is a set containing every `f`-value
and avoiding every `g`-value. Injectivity is part of the source principle, so it
lives in the capability itself, not in a consumer's input adapter.

**Bridge-local and deliberately UNREGISTERED**: no statement variant, no fact, no
alias. This interface exists so the 2-regular matching reversal can factor
through it exactly as in the source — perfect matching ⟹ disjoint-range
separation ⟹ WKL — and so the future relative-Σ⁰₁-separation front (fact six)
arrives with a worked consumer before any registration decision. Nothing here
enters any certified count.

Everything is relational through `InternalFunction.MapsTo` and set membership —
`eval` never enters a statement (the statement-burden gate in
`scripts/MetaSmoke.lean` pins this). `DisjointRangeSeparationAt Ω` carries no
base-theory premise, exactly like the registered capabilities.
-/

namespace ReverseMathlib.Omega

/-- The graph-coded function is injective: distinct arguments never share a
value. Relational — the graph-level form of `Function.Injective`. -/
def InternalFunction.IsInjective {Ω : OmegaPart} (f : InternalFunction Ω) : Prop :=
  ∀ m m' v, f.MapsTo m v → f.MapsTo m' v → m = m'

/-- The two functions' ranges are disjoint: no value is hit by both. -/
def DisjointRanges {Ω : OmegaPart} (f g : InternalFunction Ω) : Prop :=
  ∀ m m' v, f.MapsTo m v → g.MapsTo m' v → False

/-- `Z` separates the ranges: it contains every `f`-value and avoids every
`g`-value — exactly Hirst's `∀j ∀n ((f(j) = n → n ∈ X) ∧ (g(j) = n → n ∉ X))`. -/
def SeparatesRanges {Ω : OmegaPart} (f g : InternalFunction Ω)
    (Z : Ω.InternalSet) : Prop :=
  (∀ m v, f.MapsTo m v → v ∈ Z.1) ∧ ∀ m v, g.MapsTo m v → v ∉ Z.1

/-- Disjoint-range separation at a second-order part: every pair of internal
injections with disjoint ranges has an internal separating set. The internal
form of Hirst's Theorem 1.2 (ii); no base-theory premise inside the
capability. Bridge-local, unregistered. -/
def DisjointRangeSeparationAt (Ω : OmegaPart) : Prop :=
  ∀ f g : InternalFunction Ω, f.IsInjective → g.IsInjective →
    DisjointRanges f g → ∃ Z : Ω.InternalSet, SeparatesRanges f g Z

end ReverseMathlib.Omega
