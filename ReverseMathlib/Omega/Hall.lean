/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import ReverseMathlib.Omega.Graph

/-!
# Internal countable Hall at a second-order part (issue #22, slice 4)

The internal presentation of countable Hall — the **exact input presentation**, settled
here and only now registered (see `ReverseMathlib.Ports.Omega.Catalog` for why it was
deliberately absent until this slice): an internal **candidate relation** plus an internal
**candidate enumerator** with a checked membership-equivalence property (`mem_iff`). The
relation gives the transversal's target its meaning; the enumerator makes each candidate
set explicitly finite, mirroring the ambient `t : ℕ → Finset ℕ` presentation
(`ReverseMathlib.Standard.CountableHall`) without hiding ambient data in the bundle.

Everything is stated relationally through `InternalFunction.MapsTo` and set membership —
`eval` never enters a statement (the statement-burden gate in `scripts/MetaSmoke.lean`
pins this). The marriage condition quantifies over *witnessed* enumerator codes, so no
selection appears in the statement.

`CountableHallAt Ω` carries no base-theory premise, exactly like `WeakKonigAt` and
`EFILCAt`.
-/

namespace ReverseMathlib.Omega

/-- An internally presented countable Hall family: an internal candidate relation (codes
`Nat.pair n y` meaning `y` is a candidate for index `n`) and a graph-coded internal
enumerator (`enum.MapsTo n c` says `c` codes the explicit duplicate-free list of the
candidates of `n`), tied together by the checked membership-equivalence property
`mem_iff`. -/
structure InternalHallFamily (Ω : OmegaPart) where
  /-- The candidate relation, as an internal set of `Nat.pair n y` codes. -/
  relation : Ω.InternalSet
  /-- The candidate enumerator: index `n` ↦ code of the explicit finite candidate list. -/
  enum : InternalFunction Ω
  /-- Every enumerated candidate list is duplicate-free — an explicit enumeration. -/
  enum_nodup : ∀ n c, enum.MapsTo n c → (decodeSeq c).Nodup
  /-- **The checked membership equivalence**: the enumerator enumerates exactly the
  relation's candidates. -/
  mem_iff : ∀ n c y, enum.MapsTo n c → (y ∈ decodeSeq c ↔ Nat.pair n y ∈ relation.1)

/-- The marriage condition, relationally: every finite index set has at least as many
combined enumerated candidates as members. The enumerator codes enter only through
witnesses (`MapsTo`), never through evaluation. -/
def InternalHallFamily.MarriageCondition {Ω : OmegaPart} (H : InternalHallFamily Ω) :
    Prop :=
  ∀ (s : Finset ℕ) (w : ℕ → ℕ), (∀ n ∈ s, H.enum.MapsTo n (w n)) →
    s.card ≤ (s.biUnion fun n => (decodeSeq (w n)).toFinset).card

/-- `f` is an injective internal transversal of the family: every value is a candidate of
its index (through the **relation**), and no value is chosen twice. Relational
throughout. -/
def InternalHallFamily.IsTransversal {Ω : OmegaPart} (H : InternalHallFamily Ω)
    (f : InternalFunction Ω) : Prop :=
  (∀ n y, f.MapsTo n y → Nat.pair n y ∈ H.relation.1) ∧
    ∀ n n' y, f.MapsTo n y → f.MapsTo n' y → n = n'

/-- Countable Hall at a second-order part: every internally presented family satisfying
the marriage condition has an injective internal transversal. No base-theory premise
inside the capability. -/
def CountableHallAt (Ω : OmegaPart) : Prop :=
  ∀ H : InternalHallFamily Ω, H.MarriageCondition →
    ∃ f : InternalFunction Ω, H.IsTransversal f

end ReverseMathlib.Omega
