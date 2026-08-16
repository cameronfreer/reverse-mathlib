/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Jump
import ReverseMathlib.Omega.RangeSeparation

/-!
# Jump closure ⇔ injection-range existence at a second-order part (issue #49)

The two statement capabilities and the two direction theorems of the seventh
certified ω-fact:

* `JumpClosedAt Ω` — a **semantic closure property**: the jump of every internal set
  is internal. Not a theorem-strength principle; it names the closure condition that
  distinguishes the jump ideals among the Turing ideals (Hirst, thesis §1.4: "the set
  domains of ω-models of ACA₀ are called jump ideals").
* `InjectionRangeExistenceAt Ω` — every internal graph-coded **injective** function
  has an internal range, at the exact injection-graph presentation of
  `InternalFunction` (the presentation the sixth certified fact froze).

Both directions are over the Turing-ideal closure conditions:

* jump closure → range existence: the range of an internal injection is one
  `range_le_jump` reduction below the jump of its graph, and the ideal is downward
  closed;
* range existence → jump closure: the jump enumeration's graph is internal
  (`jumpEnumGraph_le` plus downward closure), packages as a total injective
  `InternalFunction`, and its internal range **is** the jump set (`range_jumpEnum`).

Route discipline (gated in `scripts/MetaSmoke.lean`): each direction goes through its
own reduction spine and never through the opposite direction theorem. No "ACA" label
appears anywhere: no arithmetical-comprehension adapter is proved, and the
identification of jump ideals with ACA₀'s ω-models stays a literature-backed reading.
-/

namespace ReverseMathlib.Omega

/-- **Jump closure** at a second-order part — a semantic closure property, never a
theorem-strength principle: the jump of every internal set is internal. -/
def JumpClosedAt (Ω : OmegaPart) : Prop :=
  ∀ A : Ω.InternalSet, jumpSet A.1 ∈ Ω

/-- **Injection-range existence** at a second-order part, at the exact
injection-graph presentation: every internal graph-coded injective function has an
internal range. Relational throughout (`MapsTo`, membership), like every registered
capability. -/
def InjectionRangeExistenceAt (Ω : OmegaPart) : Prop :=
  ∀ f : InternalFunction Ω, f.IsInjective →
    ∃ R : Ω.InternalSet, ∀ v, v ∈ R.1 ↔ ∃ m, f.MapsTo m v

/-- **Jump closure gives injection-range existence** over the Turing-ideal closure
conditions: the range of an internal injection is a single `range_le_jump` reduction
below the jump of its graph. -/
theorem injectionRangeExistenceAt_of_jumpClosedAt {Ω : OmegaPart}
    (hΩ : IsTuringIdeal Ω) (hJ : JumpClosedAt Ω) : InjectionRangeExistenceAt Ω := by
  intro f _hf
  have hmem : {v : ℕ | ∃ m, Nat.pair m v ∈ f.graph.1} ∈ Ω :=
    hΩ.mem_of_reducible (hJ f.graph) (range_le_jump f.graph.1)
  exact ⟨⟨_, hmem⟩, fun v => Iff.rfl⟩

/-- **Injection-range existence gives jump closure** over the Turing-ideal closure
conditions: the jump enumeration's graph is internal, packages as a total injective
internal function, and its internal range is exactly the jump set. -/
theorem jumpClosedAt_of_injectionRangeExistenceAt {Ω : OmegaPart}
    (hΩ : IsTuringIdeal Ω) (hR : InjectionRangeExistenceAt Ω) : JumpClosedAt Ω := by
  intro A
  -- the enumeration's graph is internal
  have hgmem : {q : ℕ | jumpEnum A.1 q.unpair.1 = q.unpair.2} ∈ Ω :=
    hΩ.mem_of_reducible A.2 (jumpEnumGraph_le A.1)
  -- package the total injective internal function
  let f : InternalFunction Ω :=
    { graph := ⟨_, hgmem⟩
      total := fun x => ⟨jumpEnum A.1 x, by
        simp [Set.mem_setOf_eq, Nat.unpair_pair]⟩
      singleValued := fun x y y' hy hy' => by
        simp only [Set.mem_setOf_eq, Nat.unpair_pair] at hy hy'
        rw [← hy, ← hy'] }
  have hinj : f.IsInjective := by
    intro m m' v hm hm'
    simp only [InternalFunction.MapsTo, f, Set.mem_setOf_eq, Nat.unpair_pair]
      at hm hm'
    exact jumpEnum_injective A.1 (hm.trans hm'.symm)
  obtain ⟨R, hRspec⟩ := hR f hinj
  -- the internal range is the jump set
  have hEq : R.1 = jumpSet A.1 := by
    ext v
    rw [hRspec v, ← range_jumpEnum A.1]
    constructor
    · rintro ⟨m, hm⟩
      simp only [InternalFunction.MapsTo, f, Set.mem_setOf_eq, Nat.unpair_pair] at hm
      exact ⟨m, hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, by
        simp only [InternalFunction.MapsTo, f, Set.mem_setOf_eq, Nat.unpair_pair]
        exact hm⟩
  exact hEq ▸ R.2

end ReverseMathlib.Omega
