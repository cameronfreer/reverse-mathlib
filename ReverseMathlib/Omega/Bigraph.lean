/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Graph

/-!
# Internal 2-regular bipartite graphs and perfect matching at a second-order part
(issue #42, slice 1)

The **enumerated-neighborhood** presentation of the two-sided 2-regular
perfect-matching principle: a common internal edge set together with two exact
neighbor enumerators, one per side, each carrying a checked membership-equivalence
property (`mem_iff`) against the **same** edge set — that shared target is the
two-sided coherence, and no separate coherence axiom exists. Regularity is a checked
property of the *supplied* enumerators (nodup lists of length exactly two), so the
presentation is data-bearing exactly as EFILC's fibers and Hall's candidate
enumerator are.

This variant is deliberately **presentation-sensitive**: it is a supplied-enumerator
refinement of the literature's abstract countable 2-regular bipartite graph
(Shafer §6.1 / Hirst; Simpson X.3.16-adjacent), not automatically identical to it —
no classification transfers between the two without a proved presentation bridge,
and the recorded `perfectMatchingToOneSidedOmega` bridge stays MISSING.

A perfect matching is a total internal graph-coded function that is edge-respecting,
injective, and **right-surjective** — genuinely two-sided, unlike
`InternalHallFamily.IsTransversal`, which saturates the index side only. There is
**no marriage-condition hypothesis**: two-sided 2-regularity itself is the
matchability certificate, which is exactly why this variant carries content.

Everything is stated relationally through `InternalFunction.MapsTo` and set
membership — `eval` never enters a statement (the statement-burden gate in
`scripts/MetaSmoke.lean` pins this). `TwoRegularPerfectMatchingAt Ω` carries no
base-theory premise, exactly like `WeakKonigAt`, `EFILCAt`, and `CountableHallAt`.
-/

namespace ReverseMathlib.Omega

/-- An internally presented two-sided 2-regular bipartite graph: a common internal
edge set (codes `Nat.pair n y` for left vertex `n` adjacent to right vertex `y`) and
two exact neighbor enumerators. Each enumerator returns the code of the explicit
nodup list of the vertex's neighbors on the other side, checked against the shared
edge set by its `mem_iff` field; each list has length exactly two. -/
structure InternalTwoRegularBigraph (Ω : OmegaPart) where
  /-- The edge set: an internal set of `Nat.pair n y` codes (left `n`, right `y`). -/
  edges : Ω.InternalSet
  /-- The left neighbor enumerator: left vertex `n` ↦ code of the explicit list of
  its right-neighbors. -/
  leftEnum : InternalFunction Ω
  /-- The right neighbor enumerator: right vertex `y` ↦ code of the explicit list of
  its left-neighbors. -/
  rightEnum : InternalFunction Ω
  /-- Every decoded left-neighbor list is duplicate-free. -/
  leftEnum_nodup : ∀ n c, leftEnum.MapsTo n c → (decodeSeq c).Nodup
  /-- Every decoded right-neighbor list is duplicate-free. -/
  rightEnum_nodup : ∀ y c, rightEnum.MapsTo y c → (decodeSeq c).Nodup
  /-- The left enumeration describes exactly the shared edge set. -/
  left_mem_iff : ∀ n c y, leftEnum.MapsTo n c →
    (y ∈ decodeSeq c ↔ Nat.pair n y ∈ edges.1)
  /-- The right enumeration describes exactly the shared edge set. -/
  right_mem_iff : ∀ y c n, rightEnum.MapsTo y c →
    (n ∈ decodeSeq c ↔ Nat.pair n y ∈ edges.1)
  /-- Every left vertex has exactly two enumerated neighbors. -/
  left_two_regular : ∀ n c, leftEnum.MapsTo n c → (decodeSeq c).length = 2
  /-- Every right vertex has exactly two enumerated neighbors. -/
  right_two_regular : ∀ y c, rightEnum.MapsTo y c → (decodeSeq c).length = 2

/-- `f` is a perfect matching of `G`: a graph-coded internal function that is
edge-respecting, injective, and right-surjective — every right vertex is matched, so
the matching saturates **both** sides (totality of `f` saturates the left side).
Stated relationally — no selection, no `eval`. -/
def InternalTwoRegularBigraph.IsPerfectMatching {Ω : OmegaPart}
    (G : InternalTwoRegularBigraph Ω) (f : InternalFunction Ω) : Prop :=
  (∀ n y, f.MapsTo n y → Nat.pair n y ∈ G.edges.1) ∧
    (∀ n n' y, f.MapsTo n y → f.MapsTo n' y → n = n') ∧
    ∀ y, ∃ n, f.MapsTo n y

/-- Two-sided 2-regular perfect matching at a second-order part: every internally
presented 2-regular bipartite graph has an internal perfect matching. No marriage
condition — two-sided 2-regularity is itself the matchability certificate. The
Turing-ideal presentation of the ω-model layer; no base-theory premise inside the
capability. -/
def TwoRegularPerfectMatchingAt (Ω : OmegaPart) : Prop :=
  ∀ G : InternalTwoRegularBigraph Ω, ∃ f : InternalFunction Ω, G.IsPerfectMatching f

end ReverseMathlib.Omega
