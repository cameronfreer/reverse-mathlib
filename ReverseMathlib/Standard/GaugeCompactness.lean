/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.SetNotation

/-!
# Gauge compactness and hidden-uniformity Heine statements (issue #70, tranche 1)

Ambient statements only. The gauge (canonical-cover) compactness of the unit interval
in the shape of [NS18]'s HBU — `(∀Ψ : ℝ → ℝ⁺)(∃⟨y₁, …, y_k⟩)(∀x ∈ I)(∃i ≤ k)(x ∈
(y_i − Ψ(y_i), y_i + Ψ(y_i)))` — and the **hidden-uniformity Heine principle** of
[NS18] Corollary A.2: for every positive gauge `g` and tolerance `ε` there is one `δ`
that is a uniform modulus for **every** function admitting `g` as a pointwise
modulus. The quantifier order `∀ g, ∃ δ, ∀ f` is the content: `δ` depends only on the
local-control data, never on the controlled function — a strictly stronger dependency
statement than ordinary Heine–Cantor, which the ordinary statement hides.

Presentation choices, pinned:

* the subcover is an **indexed finite family** with centers in the interval by type
  (`Fin (size + 1) → UnitInterval`), matching the source's finite sequence of centers
  and its canonical covering indexed by points of the interval — never a `Finset ℝ`,
  whose decidable equality and duplicate elimination on reals are exactly the kind of
  silent presentation cost these statements exist to expose;
* all inequalities are **strict**, as in the source;
* gauges and moduli are **totalized ambient presentations** `ℝ → ℝ → ℝ`: values
  outside `[0, 1] × (0, ∞)` are ignored by every property below, so this is a
  totalization of the source's `g : (I × ℝ⁺) → ℝ⁺`, not a literal identity with it.

These are ambient factorization interfaces over unrestricted Lean reals — no RM
semantic scope, no computational calibration, and nothing here enters the certified
ω scoreboard.
-/

namespace ReverseMathlib.Standard

/-- The unit interval, as the ambient set `[0, 1] ⊆ ℝ`. -/
abbrev UnitInterval : Set ℝ := Set.Icc (0 : ℝ) 1

/-- A finite subcover of the canonical covering `⋃_{x ∈ [0,1]} (x − Ψ x, x + Ψ x)`:
a nonempty indexed family of centers in the interval (by type) whose `Ψ`-balls cover
it. The finite-sequence shape of [NS18]'s HBU; no equality test on reals enters. -/
structure GaugeSubcover (Ψ : ℝ → ℝ) where
  /-- One less than the number of centers — the family is nonempty by type. -/
  size : ℕ
  /-- The centers, in the interval by type. -/
  center : Fin (size + 1) → UnitInterval
  /-- Every point of the interval lies strictly within some center's radius. -/
  covers : ∀ y : UnitInterval, ∃ i, |y.1 - (center i).1| < Ψ (center i).1

/-- Gauge (canonical-cover) compactness of the unit interval — the HBU shape of
[NS18]: every gauge positive on the interval admits a finite subcover of its
canonical covering. An ambient capability interface; unrestricted Lean proves it
outright (`ReverseMathlib.Classical`), and the point of naming it is the
factorization, never a calibration. -/
def GaugeHeineBorelOnUnitInterval : Prop :=
  ∀ Ψ : ℝ → ℝ, (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < Ψ x) → Nonempty (GaugeSubcover Ψ)

/-- `g` is positive on the interval at every positive tolerance — the gauge
positivity a capability application needs before any controlled function exists. -/
def IsPositiveGaugeOn (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ ε > (0 : ℝ), 0 < g x ε

/-- `g` is a pointwise modulus of continuity for `f` on the interval: at each point
`x` and tolerance `ε`, points strictly within `g x ε` of `x` move `f` strictly less
than `ε`. The control property alone — positivity is `IsPositiveGaugeOn`, stated
separately. -/
def IsPointwiseModulusOn (g : ℝ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ ε > (0 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) 1,
    |y - x| < g x ε → |f y - f x| < ε

/-- `δ` is a uniform modulus for `f` on the interval at tolerance `ε`. -/
def IsUniformModulusAt (δ ε : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |y - x| < δ → |f y - f x| < ε

/-- **The hidden-uniformity Heine principle** ([NS18] Corollary A.2 shape): for
every positive gauge `g` and tolerance `ε` there is one `δ` that is a uniform
modulus for **every** function admitting `g` as a pointwise modulus. The quantifier
order `∀ g, ∃ δ, ∀ f` is the content — `δ` depends only on the local-control data.
Distinct from ordinary Heine–Cantor, whose statement conceals this dependency. -/
def UniformHeineOnUnitInterval : Prop :=
  ∀ g : ℝ → ℝ → ℝ, IsPositiveGaugeOn g → ∀ ε > (0 : ℝ),
    ∃ δ, 0 < δ ∧ ∀ f : ℝ → ℝ, IsPointwiseModulusOn g f → IsUniformModulusAt δ ε f

end ReverseMathlib.Standard
