/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Standard.GaugeCompactness
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith

/-!
# The hidden-uniformity Heine theorem from gauge compactness (issue #70, tranche 1)

The relative proof: gauge (canonical-cover) compactness of the unit interval gives
the hidden-uniformity Heine principle. The chosen `δ` is the **named, isolated
construction** `gaugeUniformDelta` — a Type-level function of the supplied finite
subcover and the gauge, never of any controlled function; describing it as a
construction from supplied data is a statement about parameter dependence, **not** a
computability result. The proof is the standard overlap argument: cover by half-radius
balls at tolerance `ε / 2`, take `δ` as the least half-radius; a point and its
`δ`-neighbor then share a center within its full radius, so both function values sit
strictly within `ε / 2` of the center's value.

Route discipline (gated in `scripts/MetaSmoke.lean`): this proof reaches
`gaugeUniformDelta` and reaches **none** of mathlib's packaged compactness — no
`IsCompact`, no `isCompact_Icc`, no finite-subcover API, no
`CompactSpace.uniformContinuous_of_continuous`. The capability hypothesis replaces
that machinery entirely; unrestricted Lean's outright proof of the capability lives in
`ReverseMathlib.Classical`, a different file with the mirror-image gates.
-/

namespace ReverseMathlib.Slice

open ReverseMathlib.Standard

/-- The uniform modulus a finite gauge subcover induces: the least half-radius
`g c (ε / 2) / 2` over the subcover's centers. A Type-level construction from the
supplied subcover and gauge — its inputs are exactly the local-control data, so the
value cannot depend on any controlled function. -/
noncomputable def gaugeUniformDelta {Ψ : ℝ → ℝ} (g : ℝ → ℝ → ℝ) (ε : ℝ)
    (C : GaugeSubcover Ψ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => g (C.center i).1 (ε / 2) / 2

/-- **The hidden-uniformity Heine theorem**: gauge compactness gives the
`∀ g, ∃ δ, ∀ f` principle — one `δ`, depending only on the gauge and the tolerance
through `gaugeUniformDelta`, uniform over every function admitting the gauge as a
pointwise modulus ([NS18] Corollary A.2 shape). An ambient factorization over
unrestricted Lean reals; no RM semantic scope and no computational claim. -/
theorem uniformHeine_of_gaugeHeineBorel (hHB : GaugeHeineBorelOnUnitInterval) :
    UniformHeineOnUnitInterval := by
  intro g hg ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- the half-radius gauge at tolerance ε / 2 is positive on the interval
  obtain ⟨C⟩ := hHB (fun x => g x (ε / 2) / 2) fun x hx => by
    have := hg x hx (ε / 2) hε2
    linarith
  refine ⟨gaugeUniformDelta g ε C, ?_, ?_⟩
  · -- the least half-radius over the finitely many centers is positive
    rw [gaugeUniformDelta, Finset.lt_inf'_iff]
    intro i _
    have := hg (C.center i).1 (C.center i).2 (ε / 2) hε2
    linarith
  · intro f hf x hx y hy hxy
    -- the center covering x controls both x and its δ-neighbor y
    obtain ⟨i, hi⟩ := C.covers ⟨x, hx⟩
    have hc : (C.center i).1 ∈ Set.Icc (0 : ℝ) 1 := (C.center i).2
    have hgc : 0 < g (C.center i).1 (ε / 2) := hg _ hc (ε / 2) hε2
    have hδle : gaugeUniformDelta g ε C ≤ g (C.center i).1 (ε / 2) / 2 :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have hxc : |x - (C.center i).1| < g (C.center i).1 (ε / 2) := by
      have : |x - (C.center i).1| < g (C.center i).1 (ε / 2) / 2 := hi
      linarith
    have hyc : |y - (C.center i).1| < g (C.center i).1 (ε / 2) := by
      have htri : |y - (C.center i).1| ≤ |y - x| + |x - (C.center i).1| :=
        abs_sub_le y x (C.center i).1
      have hyx : |y - x| < g (C.center i).1 (ε / 2) / 2 := lt_of_lt_of_le hxy hδle
      have hxc2 : |x - (C.center i).1| < g (C.center i).1 (ε / 2) / 2 := hi
      linarith
    have hfx : |f x - f (C.center i).1| < ε / 2 := hf _ hc (ε / 2) hε2 x hx hxc
    have hfy : |f y - f (C.center i).1| < ε / 2 := hf _ hc (ε / 2) hε2 y hy hyc
    have htri : |f y - f x| ≤ |f y - f (C.center i).1| + |f (C.center i).1 - f x| :=
      abs_sub_le (f y) (f (C.center i).1) (f x)
    rw [abs_sub_comm (f (C.center i).1) (f x)] at htri
    linarith

end ReverseMathlib.Slice
