/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.Equivalence
import ReverseMathlib.Omega.BigraphEquivalence
import ReverseMathlib.Omega.SeparationGadgetDecode
import ReverseMathlib.Omega.SeparationToPath
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The sixth production ω fact: disjoint-range separationω ⇔ WKLω
(issue #46)

The **atomic registration**: the disjoint-range separation interface — built
bridge-local during the matching tranche and now carrying worked artifacts on
both sides — graduates to a registered concept and certified fact. Both
directions were already frozen; this tranche is a presentation decision and
registration only.

**Presentation discipline** (pinned in review): the registered variant is the
**exact injection-graph presentation** — two graph-coded internal injections
with disjoint ranges, an internal separating set, injectivity in the capability
(Hirst thesis, Theorem 1.2 (ii), consulted in the primary source). It is
deliberately NOT labeled generic "Σ⁰₁ separation": range separation for
formula-coded Σ⁰₁ definitions, arbitrary functions, or enumerations would be
equivalent only after proving the relevant adapters, and none is proved here.

Routes, each already frozen:

* **separation → WKL**: `weakKonigAt_of_disjointRangeSeparationAt` — the
  independent tree-to-injections calibration (matching slice 5);
* **WKL → separation**: `matching_separates ∘
  twoRegularPerfectMatchingAt_of_efilcAt ∘ efilcAt_of_weakKonigAt` — through
  the EFILC equivalence, the mate-table compiler, and the Shafer gadget.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_concept disjointRangeSeparation where
  statement := "Disjoint-range separation: for every pair of injections with disjoint \
    ranges there is a separating set that contains every value of the first injection \
    and no value of the second"
  description := "Disjoint-range separation as a conceptual family: separating \
    sets for pairs of injections with disjoint ranges (Hirst Thm 1.2 (ii) / \
    Simpson's Σ⁰₁-separation circle). The registered presentation is the exact \
    injection-graph form; formula-coded Σ⁰₁ separation, arbitrary-function, and \
    enumeration presentations join only once their adapters are proved"

rm_statement_variant disjointRangeSeparation.injectionGraphs.turingIdealOmega where
  concept := disjointRangeSeparation
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.DisjointRangeSeparationAt
  description := "Disjoint-range separation at a second-order part: every pair \
    of graph-coded internal injections with disjoint ranges has an internal \
    separating set containing every f-value and avoiding every g-value; \
    injectivity is part of the capability, all stated relationally. The exact \
    injection-graph presentation — never generic Σ⁰₁ separation"

/-- **The exact ω-model equivalence certificate**: over every Turing ideal,
disjoint-range separation holds iff WKLω does. Visibly composed from the four
named frozen theorems — `weakKonigAt_of_disjointRangeSeparationAt` forward from
separation, and `matching_separates ∘ twoRegularPerfectMatchingAt_of_efilcAt ∘
efilcAt_of_weakKonigAt` back — and nothing else; the dependency gates in
`scripts/MetaSmoke.lean` require this proof to reach all four. -/
theorem disjointRangeSeparation_wkl_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal
      DisjointRangeSeparationAt WeakKonigAt :=
  ⟨fun _ h => ⟨fun hsep => weakKonigAt_of_disjointRangeSeparationAt h hsep,
    fun hw => matching_separates h
      (twoRegularPerfectMatchingAt_of_efilcAt h (efilcAt_of_weakKonigAt h hw))⟩⟩

rm_fact disjointRangeSeparationWklOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [disjointRangeSeparation.injectionGraphs.turingIdealOmega]
  rhs := [wkl.binaryTree.turingIdealOmega]
  note := "Over every Turing ideal, the injection-graph disjoint-range \
    separation and binary-tree WKL variants are equivalent at the Turing-ideal \
    ω layer. Both directions were proved before this statement was recorded, \
    each through its own route. The presentation is \
    exactly injection graphs: no formula-coded Σ⁰₁ adapter is proved, and no \
    generic Σ⁰₁-separation claim is made"

revmath_certify_fact disjointRangeSeparationWklOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.disjointRangeSeparation_wkl_omega_equivalence
  note := "Composed from four named theorems: \
    weakKonigAt_of_disjointRangeSeparationAt (separation → WKL, the independent \
    tree-to-injections calibration) and matching_separates ∘ \
    twoRegularPerfectMatchingAt_of_efilcAt ∘ efilcAt_of_weakKonigAt (WKL → \
    separation); all route architectures and this composition are pinned by \
    dependency gates in scripts/MetaSmoke.lean"

end ReverseMathlib.Ports
