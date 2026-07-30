/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Basic

/-!
# Explicit finite inverse-limit compactness

The compactness principle at the heart of the Hall walking slice, stated over standard `ℕ` in
the `ReverseMathlib.Standard` namespace. The namespace is deliberate: everything here is an
**ambient-Lean** statement about standard natural numbers, provable outright in Lean, and
carries no reverse-mathematical semantic scope. Its role is to serve as a named hypothesis for
relative theorems (`ReverseMathlib.Slice.*`) whose proof terms factor through it; model-relative
forms live in a future `ReverseMathlib.OmegaModel` namespace, never here.

Presentation is data-bearing on purpose: fibers are explicitly enumerated `Finset ℕ`s — supplied
finite data, not a bare `Finite` instance — because reverse-mathematical strength is sensitive
to exactly this difference. Bonding maps are given for **adjacent** levels only; iterating them
supplies all longer restrictions, so no identity or composition laws are needed and no
categorical plumbing arises.

**What the principle says.** EFILC — *explicit finite inverse-limit compactness* — asserts
that every sequential inverse system of explicitly enumerated, nonempty finite sets with
adjacent bonding maps has a coherent section: a choice of one element per level, each
restricting to the previous. It is "compactness for systems of finite approximations", and
it is the exact boundary the refactored Hall proof factors through: finite Hall shows every
level of coded partial transversals is nonempty; EFILC threads a coherent infinite
transversal through them (`Slice/HallFromCompactness.lean`). Kernel-checked ambient facts:
`WeakKonig ⇄ EFILC` (both directions, via the chunk-coding bridges in
`Slice/WeakKonigEfilc.lean`) and `EFILC → CountableHall`.

**Why "explicit" carries the strength.** The supplied enumerations are what keep the
principle at the WKL₀ level of the intended calibration: a version whose fibers are merely
asserted finite would force the weak system to *recover* enumeration data, drifting toward
ACA₀-level behavior — the same phenomenon as bounded vs merely finitely-branching Kőnig
(`Standard/Trees.lean`).

**The ω form.** `Omega/InverseSystem.lean` defines `EFILCAt : OmegaPart → Prop`, the
Turing-ideal internalization: the system is presented by graph-coded internal functions
(fiber enumerations as nodup finite-list codes, bonding maps relationally), and the section
must itself be an internal graph-coded function of the second-order part. The planned first
exact certified ω-model calibration is `WKLω ↔ EFILCω` (`WKL₀ ⊨ω`, never `⊢`) — proving
the walking-slice transformations are Turing reductions, so tree, path, and section stay
inside the model.
-/

namespace ReverseMathlib.Standard

/-- A sequential inverse system of explicitly finite, explicitly nonempty sets of naturals:
level `n` is the `Finset` `fiber n`, and each element of level `n + 1` restricts to an element
of level `n`. Only adjacent bonding maps are given; longer restrictions arise by iteration, so
no coherence laws are required. -/
structure ExplicitFiniteInverseSystem where
  /-- The explicitly enumerated finite set at each level. -/
  fiber : ℕ → Finset ℕ
  /-- The bonding map from level `n + 1` to level `n`. -/
  restrict : ∀ n, {x // x ∈ fiber (n + 1)} → {x // x ∈ fiber n}
  /-- Every level is (explicitly) nonempty. -/
  nonempty : ∀ n, (fiber n).Nonempty

/-- A section of the system: a choice `s n` in every fiber, coherent under the bonding maps. -/
def ExplicitFiniteInverseSystem.HasSection (F : ExplicitFiniteInverseSystem) : Prop :=
  ∃ s : ℕ → ℕ, ∃ h : ∀ n, s n ∈ F.fiber n,
    ∀ n, (F.restrict n ⟨s (n + 1), h (n + 1)⟩ : {x // x ∈ F.fiber n}).val = s n

/-- Explicit finite inverse-limit compactness: every explicitly finite, explicitly nonempty
sequential inverse system has a section. In ambient Lean this proposition is provable outright;
its role is to be taken as a *hypothesis* by relative theorems, whose proof terms then visibly
factor through it. -/
def ExplicitFiniteInverseLimitCompactness : Prop :=
  ∀ F : ExplicitFiniteInverseSystem, F.HasSection

end ReverseMathlib.Standard
