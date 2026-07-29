/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Basic
import ReverseMathlib.Slice.HallFromCompactness
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Meta.Commands

/-!
# Port record: countable Hall

The registry record of the Hall walking slice, relating mathlib's infinite Hall theorem
(`Finset.all_card_le_biUnion_card_iff_exists_injective`) to `Standard.CountableHall` and its
relative proof. The verdict is deliberately modest and precise:

* the relative Lean factorization is **kernel checked** — via the typed certificate below,
  whose type ties it to the registered principle interface and port statement;
* its ambient is **unrestricted Lean over standard ℕ**, with **no** RM semantic scope;
* the classical classification is **claimed** literature only, `UNVERIFIED`;
* backend RM certificate and exact lower bound are **pending**.

This file also registers the compactness boundary as a frontier declaration, so
`#rm_frontier` on mathlib's proof exhibits the cut.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib

/-- The typed certificate of the walking slice: its *type* asserts exactly that the registered
principle interface implies the registered port statement, so registration-time definitional
matching can verify what is being certified. -/
theorem countableHallRelativeCertificate :
    Meta.RelativeCertificate Standard.ExplicitFiniteInverseLimitCompactness
      Standard.CountableHall :=
  ⟨Slice.countableHall_of_finiteInverseLimitCompactness⟩

attribute [rm_frontier] nonempty_sections_of_finite_inverse_system

rm_principle explicitFiniteInverseLimitCompactness where
  description := "Every explicitly finite, explicitly nonempty sequential inverse system of \
    naturals has a section (adjacent bonding maps, Finset fibers)."
  interface := ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness
  claimedClassical := "equivalent to WKL₀ over RCA₀ for coded systems (cf. Simpson, SOSOA, via \
    bounded Kőnig's lemma; presentation-sensitive)"

revmath_port countableHall where
  mathlib := Finset.all_card_le_biUnion_card_iff_exists_injective
  port := ReverseMathlib.Standard.CountableHall
  relation := minedArchitecture
  claimedClassical := "WKL₀ for this explicitly-Finset presentation (cf. Hirst, marriage \
    theorems; presentation-sensitive)"
  note := "Mined from mathlib's proof: finite Hall reused for level nonemptiness; the \
    topological compactness boundary (nonempty_sections_of_finite_inverse_system, ultimately \
    Tychonoff) and the hallMatchingsOn selection scaffolding replaced by the EFILC hypothesis \
    over explicitly enumerated Finset fibers — no Nonempty-instance extraction step remains \
    (occurrence-level fact; see scripts/MetaSmoke.lean for the constant-level gates and the \
    recorded indefiniteDescription granularity limitation)."
  evidence relativeProof upper kernelChecked lean
    via ReverseMathlib.Ports.countableHallRelativeCertificate
    assumes explicitFiniteInverseLimitCompactness
    note "Proof-only closure certified by CI (scripts/MetaSmoke.lean): contains finite Hall, \
      excludes the infinite Hall theorem, the compactness boundary, and the selection \
      scaffolding."

end ReverseMathlib.Ports
