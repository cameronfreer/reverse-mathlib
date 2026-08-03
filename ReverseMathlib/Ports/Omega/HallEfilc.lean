/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Basic
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.HallFromEfilc
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The Hall ω registration: EFILCω → countable Hall ω (issue #22, slice 4)

The **atomic registration** of the Hall ω slice, in one module: the statement variant with
its now-settled exact input presentation, the typed implication fact, the exact semantic
certificate (visibly the named direction theorem, pinned by a dependency gate in
`scripts/MetaSmoke.lean`), its certification against `rca0.turingIdealOmega`, and the
linked port carrying the input-access records.

The verdict stays precisely scoped: a kernel-checked **upper** implication over every
Turing ideal — no lower bound, no equivalence, no all-model or syntactic claim, and the
context identification with RCA₀'s ω-models remains literature-backed with backend
adequacy pending.

**Input-access records** (data *consumed by the transformation*, not correctness
hypotheses), independently witnessed by the imported strong reduction
`hall_le_efilc.strongWeihrauch` — the ω theorem did not produce the Weihrauch theorem:

* **EFILCω → Hallω** — compiler `hallToSystem`: the candidate **enumerator only** (the
  candidate relation is correctness-only, enforced in the fiber compiler's type); decoder
  `sectionTransversalFunction`: the section answer only.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_statement_variant countableHall.oneSidedInjective.enumeratedCandidates.turingIdealOmega
    where
  concept := countableHall
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.CountableHallAt
  description := "Countable Hall at a second-order part, one-sided injective choice: the \
    family is an internal candidate relation plus an internal candidate enumerator with a \
    checked membership-equivalence property; the marriage condition is stated over \
    witnessed enumerator codes, and the transversal is an injective internal graph-coded \
    function, all relational"

/-- **The ω-model implication certificate**: over every Turing ideal, EFILCω implies
countable Hall ω. Visibly the named direction theorem `countableHallAt_of_efilcAt` and
nothing else; the dependency gate in `scripts/MetaSmoke.lean` requires this proof to reach
it, so registration preserves the route artifact rather than replacing it with an inline
proof. -/
theorem efilc_hall_omega_implication :
    Meta.SemanticImplicationCertificate IsTuringIdeal EFILCAt CountableHallAt :=
  ⟨fun _ h he => countableHallAt_of_efilcAt h he⟩

rm_fact efilcHallOmega implication where
  base := rca0
  scope := omegaModels
  lhs := [efilc.explicitSequential.enumeratedFibers.turingIdealOmega]
  rhs := [countableHall.oneSidedInjective.enumeratedCandidates.turingIdealOmega]
  note := "The Hall ω walking slice: an upper implication only — countable Hall's exact \
    classification at ω scope stays open (no lower bound is claimed)"

revmath_certify_fact efilcHallOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.efilc_hall_omega_implication
  note := "The named direction theorem countableHallAt_of_efilcAt; its route architecture \
    and this composition are pinned by dependency gates in scripts/MetaSmoke.lean"

revmath_port countableHallOmega where
  mathlib := Finset.all_card_le_biUnion_card_iff_exists_injective
  target := countableHall.oneSidedInjective.enumeratedCandidates.turingIdealOmega
  relation := minedArchitecture
  claimedClassical := "WKL₀ candidate at ω scope (cf. Simpson X.3; the one-sided \
    injective-choice variant is related to but not identical with X.3.15/X.3.16); upper \
    implication only, no certified lower bound"
  note := "Input access (data consumed by the transformations, not correctness \
    hypotheses). EFILCω → Hallω: compiler hallToSystem reads the candidate enumerator \
    only — the candidate relation is correctness-only, enforced in the fiber compiler's \
    type; decoder sectionTransversalFunction reads the section answer only — \
    independently witnessed by the imported strong reduction \
    hall_le_efilc.strongWeihrauch (the ω theorem did not produce the Weihrauch theorem). \
    Level nonemptiness reuses mathlib's finite Hall theorem; the infinite Hall theorem, \
    the compactness boundary, and the selection scaffolding are excluded by the route \
    gates in scripts/MetaSmoke.lean."
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    context rca0.turingIdealOmega
    via ReverseMathlib.Ports.efilc_hall_omega_implication
    assumes efilc.explicitSequential.enumeratedFibers.turingIdealOmega
    fact efilcHallOmega

end ReverseMathlib.Ports
