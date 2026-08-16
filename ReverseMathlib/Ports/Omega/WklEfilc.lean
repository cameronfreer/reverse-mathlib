/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.KonigLemma
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.Equivalence
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The first production ω fact: WKLω ⇔ EFILCω over Turing ideals (issue #22, slice 3)

The **atomic registration**: the typed equivalence fact, the exact semantic certificate
(visibly composed from the two named direction theorems, pinned by a dependency gate in
`scripts/MetaSmoke.lean`), its certification against the `rca0.turingIdealOmega` context,
and the linked port carrying the input-access records.

Two distinct claims, never conflated (see the context description): the equivalence is
kernel-checked over **every Turing ideal**; the identification of Turing ideals with the
ω-models of RCA₀ is literature-backed ([Sim09] VIII.1), with backend object-syntax adequacy
pending. Nothing here is an unqualified RM bound.

**Input-access records** (data *consumed by the transformations*, not correctness
hypotheses), each now independently witnessed by an imported checked Weihrauch reduction —
the ω theorems did not produce the Weihrauch theorems; the two lenses agree independently:

* **EFILCω → WKLω** — compiler `treeToSystem`: the input tree; decoder
  `sectionPathInternal`: the section answer only. Witnessed by the imported strong
  reduction `wkl_le_efilc.strongWeihrauch`.
* **WKLω → EFILCω** — compiler `systemToTree`: fiber graph ⊕ bonding graph; decoder
  `pathSectionFunction`: fiber graph ⊕ path answer, with bonding data correctness-only in
  the decoder (enforced in the decoder's type). Witnessed by the imported
  certified-ordinary reduction `efilc_le_wkl.weihrauch`.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

/-- **The exact ω-model equivalence certificate**: over every Turing ideal, WKLω holds iff
EFILCω does. Visibly composed from the two named direction routes —
`efilcAt_of_weakKonigAt` and `weakKonigAt_of_efilcAt` — and nothing else; the dependency
gate in `scripts/MetaSmoke.lean` requires this proof to reach both named theorems, so
registration preserves those artifacts rather than silently replacing them with an inline
proof. -/
theorem weakKonig_efilc_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal WeakKonigAt EFILCAt :=
  ⟨fun _ h => ⟨efilcAt_of_weakKonigAt h, weakKonigAt_of_efilcAt h⟩⟩

rm_fact wklEfilcOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [wkl.binaryTree.turingIdealOmega]
  rhs := [efilc.explicitSequential.enumeratedFibers.turingIdealOmega]
  note := "Over every Turing ideal, the binary-tree formulation of weak Kőnig's lemma and \
    enumerated-fiber EFILC variants are equivalent at the Turing-ideal ω layer"

revmath_certify_fact wklEfilcOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.weakKonig_efilc_omega_equivalence
  note := "Composed from the named direction theorems efilcAt_of_weakKonigAt and \
    weakKonigAt_of_efilcAt; both route architectures and this composition are pinned by \
    dependency gates in scripts/MetaSmoke.lean"

revmath_port weakKonigEfilcOmega where
  mathlib := exists_seq_forall_proj_of_forall_finite
  target := wkl.binaryTree.turingIdealOmega
  relation := conceptualAnalogue
  claimedClassical := "WKL₀-level equivalence over RCA₀ for coded presentations (cf. \
    Simpson, SOSOA; presentation-sensitive)"
  note := "Input access (data consumed by the transformations, not correctness \
    hypotheses). EFILCω → WKLω: compiler treeToSystem reads the input tree; decoder \
    sectionPathInternal reads the section answer only — independently witnessed by the \
    imported strong reduction wkl_le_efilc.strongWeihrauch. WKLω → EFILCω: compiler \
    systemToTree reads fiber graph ⊕ bonding graph; decoder pathSectionFunction reads \
    fiber graph ⊕ path answer, bonding data correctness-only in the decoder (enforced in \
    the decoder's type) — independently witnessed by the imported certified-ordinary \
    reduction efilc_le_wkl.weihrauch. The ω theorems did not produce the Weihrauch \
    theorems: the two lenses agree independently."
  evidence semanticImplication exact kernelChecked modelSemantics scope omegaModels
    context rca0.turingIdealOmega
    via ReverseMathlib.Ports.weakKonig_efilc_omega_equivalence
    assumes efilc.explicitSequential.enumeratedFibers.turingIdealOmega
    fact wklEfilcOmega

end ReverseMathlib.Ports
