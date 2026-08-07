/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Ports.Catalog
import ReverseMathlib.Omega.InverseSystem

/-!
# The Turing-ideal ω-model catalog layer (issue #22, slice 2)

Registers the `turingIdealOmega` semantic layer (interface schema `OmegaPart → Prop`), the
`rca0` base theory, the `rca0.turingIdealOmega` semantic context over `IsTuringIdeal`, and
**exactly two** presentation-explicit statement variants owning `WeakKonigAt` and `EFILCAt`.

The Hall ω variant was deliberately absent until its exact input presentation — internal
candidate relation plus internal enumerator with a checked membership-equivalence
property — was settled; it now lands, with its fact, certificate, certification, and
linked port, **together** in `ReverseMathlib.Ports.Omega.HallEfilc` (slice 4). The first
production ω fact (the WKLω ⇔ EFILCω equivalence) landed the same way in
`ReverseMathlib.Ports.Omega.WklEfilc`, exercising the complete fact-evidence pipeline
(#24).
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

/-- The interface schema of the Turing-ideal ω layer: model-indexed propositions
`OmegaPart → Prop`. Universe-monomorphic by construction. -/
abbrev OmegaInterface := ReverseMathlib.Omega.OmegaPart → Prop

rm_semantic_layer turingIdealOmega
  "statements about a second-order part Ω in the computability-theoretic (Turing-ideal) \
   presentation of the ω-model layer; capabilities are model-indexed propositions carrying \
   no base-theory premise"
  interfaceSchema := OmegaInterface

rm_base_theory rca0
  "RCA₀: Δ⁰₁ comprehension with Σ⁰₁ induction over elementary arithmetic ([Sim09] I.7)"

rm_semantic_context rca0.turingIdealOmega where
  base := rca0
  scope := omegaModels
  layer := turingIdealOmega
  decl := ReverseMathlib.Omega.IsTuringIdeal
  description := "The computability-theoretic Turing-ideal presentation of RCA₀'s ω-models. \
    Distinct claims, never conflated: an implication certified against this context is \
    kernel-checked over every Turing ideal; the identification of Turing ideals with the \
    ω-models of RCA₀ is literature-backed ([Sim09] VIII.1). Backend evidence \
    (rmFoundationBridge) adds: checked forward context realization (every Turing ideal \
    satisfies an explicit semantic RCA₀ theory on ω-structures — one-way) and checked \
    unconditional statement adapters; converse context adequacy remains pending, and the \
    backend calculus's standard-calculus comparison remains pending."

rm_statement_variant wkl.binaryTree.turingIdealOmega where
  concept := wkl
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.WeakKonigAt
  description := "Weak Kőnig's lemma at a second-order part: every internal binary tree \
    (internal set of canonical sequence codes, bit-valued and prefix-closed) with a node at \
    every level has an internal path (internal set of bit-1 positions), stated relationally"

rm_statement_variant efilc.explicitSequential.enumeratedFibers.turingIdealOmega where
  concept := explicitFiniteInverseLimitCompactness
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.EFILCAt
  description := "Explicit finite inverse-limit compactness at a second-order part: fibers \
    and bonding maps presented as graph-coded internal functions with nodup, nonempty \
    enumerated fibers; sections are internal graph-coded functions, stated relationally"

end ReverseMathlib.Ports
