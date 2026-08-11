/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.BigraphEquivalence
import ReverseMathlib.Omega.Equivalence
import ReverseMathlib.Omega.SeparationGadgetDecode
import ReverseMathlib.Omega.SeparationToPath
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The fifth production ω fact: WKLω ⇔ 2-regular perfect matchingω
(issue #42, slice 6)

The **atomic registration**: the enumerated-neighborhood 2-regular
perfect-matching variant joins the `countableHall` conceptual family, with the
typed equivalence fact, the exact semantic certificate (visibly composed from
the four named route theorems, pinned by dependency gates in
`scripts/MetaSmoke.lean`), and its certification against the
`rca0.turingIdealOmega` context. The first **cross-concept** certified
equivalence: a `wkl`-family variant on one side, a `countableHall`-family
variant on the other.

Routes, each its own frozen artifact:

* **forward** (`WKLω → matchingω`): through the frozen EFILC bridge
  (`efilcAt_of_weakKonigAt`) and the paired mate-table compiler
  (`twoRegularPerfectMatchingAt_of_efilcAt`, Shafer §6.1 Lemma 6.1.7 at
  `m = 1`);
* **reversal** (`matchingω → WKLω`): the Shafer Theorem 6.1.2 gadget and
  four-query separator (`matching_separates`), then the independent
  separation-to-path calibration
  (`weakKonigAt_of_disjointRangeSeparationAt`) — the bridge-local
  disjoint-range separation interface stays **unregistered**, consumed here
  as a composition waypoint only.

Honesty pins, unchanged: the variant is an **enumerated-neighborhood
refinement** of the literature's abstract countable 2-regular graph (Shafer
thesis §6.1, Thm 6.1.2; Hirst thesis Thms 2.3, 3.3) — presentation-sensitive,
never automatically identical; the recorded `perfectMatchingToOneSidedOmega`
presentation bridge stays MISSING and is NOT discharged by this registration
(it targets the one-sided variant); the one-sided Hall exact lower bound stays
open; no Weihrauch witnesses exist for the matching uniform problem and none
are claimed.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_statement_variant
    countableHall.twoRegularPerfectMatching.enumeratedNeighborhoods.turingIdealOmega
    where
  concept := countableHall
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.TwoRegularPerfectMatchingAt
  description := "Two-sided 2-regular perfect matching at a second-order part: a \
    common internal edge set with two exact neighbor enumerators (nodup, length \
    exactly two, each checked against the shared edge set by mem_iff); a perfect \
    matching is a total internal graph-coded function that is edge-respecting, \
    injective, and right-surjective; no marriage-condition hypothesis. An \
    enumerated-neighborhood refinement of the abstract countable 2-regular graph \
    (Shafer §6.1 / Hirst) — presentation-sensitive, never automatically identical"

/-- **The exact ω-model equivalence certificate**: over every Turing ideal,
2-regular perfect matching holds iff WKLω does. Visibly composed from the four
named route theorems — the reversal `matching_separates` ∘
`weakKonigAt_of_disjointRangeSeparationAt` through the bridge-local separation
interface, and the forward `efilcAt_of_weakKonigAt` ∘
`twoRegularPerfectMatchingAt_of_efilcAt` through the frozen EFILC bridge — and
nothing else; the dependency gates in `scripts/MetaSmoke.lean` require this
proof to reach all four, so registration preserves those artifacts rather than
silently replacing them with an inline proof. -/
theorem wkl_twoRegularMatching_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal
      TwoRegularPerfectMatchingAt WeakKonigAt :=
  ⟨fun _ h => ⟨fun hm => weakKonigAt_of_disjointRangeSeparationAt h
      (matching_separates h hm),
    fun hw => twoRegularPerfectMatchingAt_of_efilcAt h
      (efilcAt_of_weakKonigAt h hw)⟩⟩

rm_fact wklTwoRegularMatchingOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [countableHall.twoRegularPerfectMatching.enumeratedNeighborhoods.turingIdealOmega]
  rhs := [wkl.binaryTree.turingIdealOmega]
  note := "The fifth production ω fact and the first CROSS-CONCEPT certified \
    equivalence: the enumerated-neighborhood 2-regular perfect-matching variant \
    (countableHall family) and the binary-tree WKL variant are equivalent at the \
    Turing-ideal ω layer. Provenance: Shafer thesis §6.1 Thm 6.1.2, citing Hirst \
    thesis Thms 2.3 and 3.3 — proof-carrying transcription at this exact internal \
    presentation; the perfectMatchingToOneSidedOmega presentation bridge stays \
    MISSING (this variant sits on the perfect-matching side and does not \
    discharge it), and the one-sided Hall exact lower bound stays open"

revmath_certify_fact wklTwoRegularMatchingOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.wkl_twoRegularMatching_omega_equivalence
  note := "Composed from the four named route theorems: matching_separates then \
    weakKonigAt_of_disjointRangeSeparationAt (the reversal, through the \
    bridge-local unregistered disjoint-range separation interface), and \
    efilcAt_of_weakKonigAt then twoRegularPerfectMatchingAt_of_efilcAt (the \
    forward, through the frozen EFILC bridge); all route architectures and this \
    composition are pinned by dependency gates in scripts/MetaSmoke.lean"

end ReverseMathlib.Ports
