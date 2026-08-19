/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.MatchingFromKonig
import ReverseMathlib.Omega.MatchingGadget
import ReverseMathlib.Ports.Omega.Catalog
import ReverseMathlib.Ports.Omega.FinitelyBranchingKonigFact

/-!
# The tenth production ω fact: locally finite perfect matchingω ⇔ finitely-branching
Kőnigω (issue #51)

The **atomic registration**: over every Turing ideal, Hirst's symmetric marriage
theorem in its property-shaped presentation — one bare internal edge set, local
finiteness on each side as an existential property, the cardinality-form H_sym as a
separate hypothesis — holds exactly when full finitely-branching Kőnig does. The
concept and its variant are new and deliberately **separate from the `countableHall`
family and from the enumerated two-regular presentation class**: supplying neighbor
enumerators makes the partial-solution tree's level bound computable and collapses
the principle into the supplied-bound/WKL class, while the reversal gadget's
neighbor data encodes range membership and is not computable from the injection.

The registered endpoint is `finitelyBranchingKonig` — the proof-architecture-honest
choice: the forward direction literally walks the Kőnig tree, the source states the
equivalence with König's lemma via ACA₀, and jump closure stays one certified hop
away, reached in the atlas by computed closure only (registering the jump endpoint
directly would also trip the equivalence chain rule's hub bound).

**Routes** (each gated in `scripts/MetaSmoke.lean`):

* **forward** — `locallyFinitePerfectMatchingAt_of_finitelyBranchingKonigAt`:
  Hirst's partial-solution tree — internality by `solutionTree_le_graph`, finite
  branching from the two local-finiteness properties, infinitude by the finite
  symmetric-Hall covering lemma (`exists_matching_covering`, reused from the fifth
  fact's finite layer), and the path decoder. No jump and no reversal machinery.
* **reverse**, in two named stages, with the intermediate implication kept as proof
  architecture and never registered:
  `injectionRangeExistenceAt_of_locallyFinitePerfectMatchingAt` (Hirst's gadget —
  internality by `marriageGadgetEdgeSet_le_graph`, H_sym by the injective canonical
  neighbor choice, the decoded range one complemented matching query or one bounded
  witness search below the join, `marriageGadgetRangeSet_le_join`), then
  `finitelyBranchingKonigAt_of_locallyFinitePerfectMatchingAt` composing through the
  seventh fact's checked direction `jumpClosedAt_of_injectionRangeExistenceAt` and
  the ninth's forward direction `finitelyBranchingKonigAt_of_jumpClosedAt`.

No ACA-labeled endpoint or fact, and no bridge to the one-sided Hall variant, the
enumerated two-regular matching, a represented problem, or a Weihrauch claim: the
standing Hall honesty boundary is untouched.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_concept locallyFinitePerfectMatching where
  statement := "Hirst's symmetric marriage theorem: every locally finite marriage \
    problem satisfying the two-sided condition H_sym has a symmetric solution — a \
    perfect matching saturating both sides"
  description := "The ACA-level matching concept (Hirst thesis Theorem 3.1 shape), \
    deliberately distinct from the countable-Hall family (one-sided, \
    enumerator-bearing) and from the enumerated two-regular perfect-matching \
    presentation class of the fifth fact: local finiteness is an existential \
    property of a bare edge set. No ACA-labeled endpoint or fact"

rm_statement_variant locallyFinitePerfectMatching.bareEdgeSet.turingIdealOmega where
  concept := locallyFinitePerfectMatching
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.LocallyFinitePerfectMatchingAt
  description := "Locally finite perfect matching at a second-order part: one bare \
    internal edge set with local finiteness on each side as an existential property \
    (never enumerators or supplied bounds), the cardinality-form H_sym as a \
    separate hypothesis, and a graph-coded internal perfect matching saturating \
    both sides, all stated relationally. Never the enumerated-neighborhood \
    presentation class, whose supplied data collapses the level bound"

/-- **The exact ω-model equivalence certificate**: over every Turing ideal, locally
finite perfect matching in its property-shaped presentation holds iff full
finitely-branching Kőnig does. Visibly composed from the two named direction
theorems — `locallyFinitePerfectMatchingAt_of_finitelyBranchingKonigAt` (the
partial-solution tree) and `finitelyBranchingKonigAt_of_locallyFinitePerfectMatchingAt`
(the gadget into injection-range existence, then the seventh fact's checked direction
and the ninth's forward direction) — and nothing else; the dependency gates in
`scripts/MetaSmoke.lean` pin both routes, the reverse's intermediate stage, and the
exclusions that keep each route clear of the other's machinery. -/
theorem locallyFinitePerfectMatching_finitelyBranchingKonig_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal
      LocallyFinitePerfectMatchingAt FinitelyBranchingKonigAt :=
  ⟨fun _ h => ⟨fun hM => finitelyBranchingKonigAt_of_locallyFinitePerfectMatchingAt h hM,
    fun hK => locallyFinitePerfectMatchingAt_of_finitelyBranchingKonigAt h hK⟩⟩

rm_fact locallyFinitePerfectMatchingKonigOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [locallyFinitePerfectMatching.bareEdgeSet.turingIdealOmega]
  rhs := [finitelyBranchingKonig.levelwiseBounded.turingIdealOmega]
  note := "Over every Turing ideal, Hirst's symmetric marriage theorem in its \
    property-shaped presentation — bare edge set, per-side local finiteness as an \
    existential property, cardinality-form H_sym — is equivalent to full \
    finitely-branching Kőnig. Provenance: Hirst thesis Theorem 3.1 (statement \
    shape verified in the pinned primary source, which proves the forward \
    direction by König's lemma for finitely branching trees, the ninth fact's \
    concept). The reversal goes through injection-range existence and the seventh \
    fact's checked direction, with the intermediate implication kept as proof \
    architecture and never registered; jump closure stays one certified hop away, \
    reached by computed closure only. No ACA-labeled endpoint or fact, and no \
    bridge to the one-sided Hall variant, the enumerated two-regular matching, a \
    represented problem, or a Weihrauch claim"

revmath_certify_fact locallyFinitePerfectMatchingKonigOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.locallyFinitePerfectMatching_finitelyBranchingKonig_omega_equivalence
  note := "Composed from the two named direction theorems: \
    locallyFinitePerfectMatchingAt_of_finitelyBranchingKonigAt (Hirst's \
    partial-solution tree: internality one reduction below the bare edge set, \
    finite branching from the local-finiteness properties, infinitude by the \
    finite symmetric-Hall covering lemma, then the path decoder) and \
    finitelyBranchingKonigAt_of_locallyFinitePerfectMatchingAt (Hirst's gadget \
    through injectionRangeExistenceAt_of_locallyFinitePerfectMatchingAt, then the \
    seventh fact's checked direction and the ninth's forward direction). \
    Dependency gates pin both route architectures, the reverse's intermediate \
    stage, and the mutual exclusions"

end ReverseMathlib.Ports
