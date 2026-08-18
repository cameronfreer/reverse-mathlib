/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.KonigFinitelyBranching
import ReverseMathlib.Ports.Omega.Catalog
import ReverseMathlib.Ports.Omega.JumpClosureFact
import ReverseMathlib.Ports.Omega.KonigJumpFact

/-!
# The ninth production ω fact: full finitely-branching Kőnigω ⇔ jump closureω
(issue #50, slice B)

The **atomic registration**: over every Turing ideal, full (merely) finitely-branching
Kőnig — the levelwise-bound **property** presentation of Hirst thesis Theorem 1.3, never
a supplied bound function — holds exactly when the part is jump closed. The concept and
its variant are new; the jump side reuses the variant registered with the seventh fact.
The explicitly bounded (supplied-data) presentation stays a separate, weaker concept:
nothing here touches the fourth fact's variant except through the certified route.

**Routes** (each gated in `scripts/MetaSmoke.lean`):

* **forward** — `finitelyBranchingKonigAt_of_jumpClosedAt`: the least level bound's
  graph is one `levelBoundGraph_le_jump` reduction below the jump of the tree; ideal
  closure internalizes it, and the eighth fact's direction theorem
  `boundedKonigAt_of_jumpClosedAt` walks the now explicitly bounded tree.
* **reverse**, in two named stages, with the intermediate implication kept as proof
  architecture and never registered:
  `injectionRangeExistenceAt_of_finitelyBranchingKonigAt` (the injection tree — nonzero
  entries name their witness by one graph query, zero entries assert no witness below
  the node's length; internality by `injectionTree_le_graph`, correctness by
  `path_determines_range`, the decoded range one complemented query), then
  `jumpClosedAt_of_finitelyBranchingKonigAt` composing through the seventh fact's
  checked direction `jumpClosedAt_of_injectionRangeExistenceAt`.

No ACA-labeled endpoint or fact: no arithmetical-comprehension adapter is proved, and
the identification of jump ideals with ACA₀'s ω-models stays a corpus-recorded
literature reading, exactly as with the seventh fact.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_concept finitelyBranchingKonig where
  statement := "Full finitely-branching Kőnig's lemma: every infinite finitely \
    branching tree has an infinite path — the branching bound is a property of the \
    tree (for every length, some bound exists on the last entries of the nodes of \
    that length), never supplied data"
  description := "The ACA-level Kőnig concept (Hirst thesis Theorem 1.3 shape: a \
    levelwise bound exists), deliberately distinct from the explicitly bounded \
    concept whose bound is supplied as data (the wkl-equivalent presentation \
    registered with the fourth fact). No ACA-labeled endpoint or fact: the \
    jump-ideal identification stays literature-backed"

rm_statement_variant finitelyBranchingKonig.levelwiseBounded.turingIdealOmega where
  concept := finitelyBranchingKonig
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.FinitelyBranchingKonigAt
  description := "Full finitely-branching Kőnig at a second-order part: an internal \
    prefix-closed set of sequence codes, levelwise bounded in the source shape (for \
    every length, a bound on the last entry of the nodes of that length — a \
    property, not data), with a node at every level, has a graph-coded internal \
    path, all stated relationally. Never the explicitly bounded presentation, whose \
    supplied bound function makes it a different (wkl-equivalent) concept"

/-- **The exact ω-model equivalence certificate**: over every Turing ideal, full
finitely-branching Kőnig holds iff the part is jump closed. Visibly composed from the
two named direction theorems — `finitelyBranchingKonigAt_of_jumpClosedAt` (the least
level bound from the jump, then the eighth fact's direction theorem) and
`jumpClosedAt_of_finitelyBranchingKonigAt` (the injection tree to range existence, then
the seventh fact's checked direction) — and nothing else; the dependency gates in
`scripts/MetaSmoke.lean` pin both routes, the two reverse stages, and the exclusions
that keep the reverse route clear of the forward machinery. -/
theorem finitelyBranchingKonig_jumpClosure_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal
      FinitelyBranchingKonigAt JumpClosedAt :=
  ⟨fun _ h => ⟨fun hK => jumpClosedAt_of_finitelyBranchingKonigAt h hK,
    fun hJ => finitelyBranchingKonigAt_of_jumpClosedAt h hJ⟩⟩

rm_fact finitelyBranchingKonigJumpOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [finitelyBranchingKonig.levelwiseBounded.turingIdealOmega]
  rhs := [jumpClosure.turingIdealClosure.turingIdealOmega]
  note := "Over every Turing ideal, full finitely-branching Kőnig in its \
    levelwise-bound property presentation is equivalent to closure under the Turing \
    jump — the ACA-level Kőnig calibration, with the bound a property and never \
    supplied data (the supplied-data presentation is the wkl-equivalent explicitly \
    bounded concept of the fourth fact). Provenance: Hirst thesis Theorem 1.3 \
    (statement shape verified in the pinned primary source; our statement carries \
    the infinitude hypothesis the thesis states separately). The reversal composes \
    through injection-range existence and the seventh fact's checked direction; the \
    intermediate implication is proof architecture, never a registered fact. No \
    ACA-labeled endpoint or fact: the jump-ideal identification stays a \
    corpus-recorded literature reading"

revmath_certify_fact finitelyBranchingKonigJumpOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.finitelyBranchingKonig_jumpClosure_omega_equivalence
  note := "Composed from the two named direction theorems: \
    finitelyBranchingKonigAt_of_jumpClosedAt (the least level bound from the jump \
    through levelBoundGraph_le_jump, then the eighth fact's direction theorem on the \
    now explicitly bounded tree) and jumpClosedAt_of_finitelyBranchingKonigAt (the \
    injection tree through injectionRangeExistenceAt_of_finitelyBranchingKonigAt — \
    internality by injectionTree_le_graph, correctness by path_determines_range — \
    then the seventh fact's jumpClosedAt_of_injectionRangeExistenceAt). Both routes, \
    the two reverse stages, and the forward/reverse exclusions are pinned by \
    dependency gates in scripts/MetaSmoke.lean"

end ReverseMathlib.Ports
