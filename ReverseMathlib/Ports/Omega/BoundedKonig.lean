/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.BoundedEquivalence
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The fourth production ω fact: bounded Kőnigω ⇔ WKLω over Turing ideals
(issue #39, slice 5)

The **atomic registration**: the explicitly bounded statement variant joins the `wkl`
conceptual family in the same tranche that fixes its relationship — the typed equivalence
fact, the exact semantic certificate (visibly composed from the two named direction
theorems, pinned by dependency gates in `scripts/MetaSmoke.lean`), and its certification
against the `rca0.turingIdealOmega` context.

Scope discipline, unchanged from the statement layer: the variant is **explicitly
bounded** — the bound is supplied data (a graph-coded internal function), never a
finite-branching property of the bare tree. Merely finitely branching (full Kőnig) is the
ACA-level principle and stays a separate concept; nothing here touches it.

**Input-access records** (data *consumed by the transformations*, not correctness
hypotheses):

* **EFILCω → bounded-Kőnigω** — compiler `boundedTreeToSystem`: the input tree ⊕ the bound
  graph (the bound only through its finite radix transcript); decoder
  `sectionBoundedPathFunction`: the section answer only.
* **bounded-Kőnigω → WKLω** — pure packaging: the constant bound's recursive graph and one
  path-graph query per position; no compiler.
* The registered converse composes through the frozen `efilcAt_of_weakKonigAt` route,
  whose input-access records are on `weakKonigEfilcOmega`.

No Weihrauch witnesses accompany this fact yet: the bounded uniform problem has no
imported reduction records, and none are claimed. -/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_statement_variant wkl.explicitlyBoundedTree.internalBoundFunction.turingIdealOmega where
  concept := wkl
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.BoundedKonigAt
  description := "Explicitly bounded Kőnig at a second-order part: an internal set of \
    sequence codes, prefix-closed, with a SUPPLIED coordinatewise bound as a graph-coded \
    internal function; paths choose one natural per position as graph-coded internal \
    functions, stated relationally. Never the finite-branching property of a bare tree — \
    full Kőnig stays a separate ACA-level concept"

/-- **The exact ω-model equivalence certificate**: over every Turing ideal, explicitly
bounded Kőnig holds iff WKLω does. Visibly composed from the two named direction routes —
`weakKonigAt_of_boundedKonigAt` (the constant-bound specialization) and
`boundedKonigAt_of_weakKonigAt` (through the frozen EFILC bridge) — and nothing else; the
dependency gates in `scripts/MetaSmoke.lean` require this proof to reach both named
theorems, so registration preserves those artifacts rather than silently replacing them
with an inline proof. -/
theorem boundedKonig_wkl_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal BoundedKonigAt WeakKonigAt :=
  ⟨fun _ h => ⟨weakKonigAt_of_boundedKonigAt h, boundedKonigAt_of_weakKonigAt h⟩⟩

rm_fact boundedKonigWklOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [wkl.explicitlyBoundedTree.internalBoundFunction.turingIdealOmega]
  rhs := [wkl.binaryTree.turingIdealOmega]
  note := "The fourth production ω fact: the explicitly bounded (supplied internal bound \
    function) and binary-tree WKL presentations are equivalent at the Turing-ideal ω \
    layer — the presentation-relating fact that lets the bounded variant join the wkl \
    conceptual family"

revmath_certify_fact boundedKonigWklOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.boundedKonig_wkl_omega_equivalence
  note := "Composed from the named direction theorems weakKonigAt_of_boundedKonigAt and \
    boundedKonigAt_of_weakKonigAt (the latter through the frozen efilcAt_of_weakKonigAt); \
    all three routes and this composition are pinned by dependency gates in \
    scripts/MetaSmoke.lean"

end ReverseMathlib.Ports
