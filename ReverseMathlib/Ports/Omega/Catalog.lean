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

Deliberately absent: a Hall ω variant (its exact input presentation — internal candidate
relation plus internal enumerator with a checked membership-equivalence property — is
settled in slice 4, never registered as an underspecified placeholder), and any fact, port,
or evidence — the first production ω fact and its certificate arrive **together** in
slice 3, after the fact-evidence linkage (#24), so the first production ω claim exercises
the complete fact-evidence pipeline.
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
    Two distinct claims, never conflated: an implication certified against this context is \
    kernel-checked over every Turing ideal; the identification of Turing ideals with the \
    ω-models of RCA₀ is literature-backed ([Sim09] VIII.1), with backend object-syntax \
    adequacy pending."

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
