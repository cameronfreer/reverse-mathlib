/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Standard.GaugeCompactness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Classical instantiation: gauge compactness outright (issue #70, tranche 1)

Unrestricted Lean proves `GaugeHeineBorelOnUnitInterval` directly from mathlib's
interval compactness (`isCompact_Icc` through `IsCompact.elim_finite_subcover`) —
the essential disclosure that the ambient capability is outright available, exactly
as `ReverseMathlib.Classical.weakKonig` discloses for the Kőnig interfaces. The
factorization in `ReverseMathlib.Slice.HeineFromGaugeCompactness` is therefore an
ambient proof-architecture statement, never a calibration.

The presentation recovery lives here and only here: mathlib returns a `Finset` of
subtype centers, and this file enumerates it into the indexed-family shape of
`GaugeSubcover` (a list walk with a default center — no equality test on reals
leaves this file). Route gates in `scripts/MetaSmoke.lean` pin that this proof
positively reaches `isCompact_Icc` and the finite-subcover API, and reaches neither
the hidden-uniformity theorem nor mathlib's Heine–Cantor theorem: it is visibly a
direct capability instantiation, not a consequence of either uniformity result.
-/

namespace ReverseMathlib.Classical

open ReverseMathlib.Standard

/-- Unrestricted Lean proves gauge compactness of the unit interval outright:
mathlib's interval compactness applied to the canonical covering, with the returned
`Finset` of centers enumerated into the indexed-family presentation. -/
theorem gaugeHeineBorelOnUnitInterval : GaugeHeineBorelOnUnitInterval := by
  classical
  intro Ψ hΨ
  -- the canonical covering by balls centered at points of the interval
  have hcov : Set.Icc (0 : ℝ) 1 ⊆ ⋃ p : UnitInterval, Metric.ball p.1 (Ψ p.1) :=
    fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hΨ x hx)⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun p : UnitInterval => Metric.ball p.1 (Ψ p.1)) (fun _ => Metric.isOpen_ball) hcov
  -- the subcover is nonempty: it covers 0
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  obtain ⟨p0, hp0, -⟩ := Set.mem_iUnion₂.mp (ht h0)
  -- enumerate the Finset into the indexed-family presentation
  refine ⟨⟨t.toList.length, fun i => t.toList.getD i.1 p0, fun y => ?_⟩⟩
  obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (ht y.2)
  have hplist : p ∈ t.toList := Finset.mem_toList.mpr hp
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hplist
  refine ⟨⟨k, by omega⟩, ?_⟩
  have hget : t.toList.getD k p0 = p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hkp]
  rw [hget]
  have : dist y.1 p.1 < Ψ p.1 := Metric.mem_ball.mp hyp
  rwa [Real.dist_eq] at this

end ReverseMathlib.Classical
