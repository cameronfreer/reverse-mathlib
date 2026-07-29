/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.KonigLemma
import ReverseMathlib.Slice.WeakKonigEfilc
import ReverseMathlib.Ports.Mathlib.Hall

/-!
# Port record: weak Kőnig ↔ explicit finite inverse-limit compactness

Registers the `weakKonig` principle and the relative equivalence with EFILC, with
direction-aware typed certificates in both directions — both **ambient Lean factorizations**
over standard ℕ with no RM semantic scope. Neither claim is an RM bound: the verdict honestly
keeps `backend RM certificate: pending` and `exact lower bound: pending`.

The mathlib counterpart recorded is `exists_seq_forall_proj_of_forall_finite`
(`Mathlib/Order/KonigLemma.lean`), the classical uncoded ℕ-indexed inverse-system Kőnig lemma —
a conceptual analogue, not an identical statement (no explicit `Finset` presentation).
-/

namespace ReverseMathlib.Ports

open ReverseMathlib

/-- Upper certificate: the EFILC interface implies the weak Kőnig statement. -/
theorem weakKonigOfEfilcCertificate :
    Meta.RelativeCertificate Standard.ExplicitFiniteInverseLimitCompactness
      Standard.WeakKonig :=
  ⟨Slice.weakKonig_of_efilc⟩

/-- Lower certificate: the weak Kőnig statement implies the EFILC interface. -/
theorem efilcOfWeakKonigCertificate :
    Meta.RelativeCertificate Standard.WeakKonig
      Standard.ExplicitFiniteInverseLimitCompactness :=
  ⟨Slice.efilc_of_weakKonig⟩

rm_principle weakKonig where
  description := "Every prefix-closed set of finite bit lists with a node at every level has \
    a path (a set of positions), on the ambient list-based surface."
  interface := ReverseMathlib.Standard.WeakKonig
  claimedClassical := "defines WKL₀ over RCA₀ for coded binary trees (Simpson, SOSOA, I.10; \
    presentation-sensitive)"

revmath_port weakKonigEfilc where
  mathlib := exists_seq_forall_proj_of_forall_finite
  port := ReverseMathlib.Standard.WeakKonig
  relation := conceptualAnalogue
  claimedClassical := "both equivalent to WKL₀ over RCA₀ for coded presentations (cf. \
    Simpson, SOSOA; presentation-sensitive)"
  note := "Ambient equivalence via chunk coding: fibers embed as fixed-width bit chunks \
    decoded by binary value modulo fiber cardinality, so chunk validity is automatic and \
    only adjacent-rank coherence constrains tree membership. Both directions are ambient \
    factorizations; neither is an RM bound."
  evidence relativeProof upper kernelChecked lean
    via ReverseMathlib.Ports.weakKonigOfEfilcCertificate
    assumes explicitFiniteInverseLimitCompactness
  evidence relativeProof lower kernelChecked lean
    via ReverseMathlib.Ports.efilcOfWeakKonigCertificate
    assumes explicitFiniteInverseLimitCompactness

end ReverseMathlib.Ports
