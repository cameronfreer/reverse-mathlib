/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Tree

/-!
# Internal explicit finite inverse systems and EFILC at a second-order part
(issue #22, slice 2)

The internal presentation of explicit finite inverse-limit compactness (see
`ReverseMathlib/Standard/InverseLimit.lean` for the ambient statement and
`ABOUT.md` for the role of EFILC in the Hall walking slice). **No external field** such as
`fiber : ℕ → Finset ℕ` appears inside the internal structure — that would be ambient data
hidden in the bundle. Instead the fibers and bonding maps are graph-coded internal functions
returning codes of nodup finite lists, so the later coherent-chain tree is computable from
internal oracle data. Everything is stated relationally through `InternalFunction.MapsTo`;
`eval` never enters a statement.

`EFILCAt Ω` carries no base-theory premise, exactly like `WeakKonigAt`.
-/

namespace ReverseMathlib.Omega

/-- An internally presented explicit finite inverse system: the fiber enumerations and the
bonding maps are graph-coded internal functions. `fibers.MapsTo n c` says `c` codes the
explicit (nodup, nonempty) list enumerating level `n`; `bonding.MapsTo (Nat.pair n x) y`
says level-`n+1` element `x` restricts to level-`n` element `y`. -/
structure InternalInverseSystem (Ω : OmegaPart) where
  /-- The fiber enumerator: level `n` ↦ code of the explicit finite list at level `n`. -/
  fibers : InternalFunction Ω
  /-- The bonding maps: `Nat.pair n x` ↦ the restriction of `x` from level `n + 1` to
  level `n`. -/
  bonding : InternalFunction Ω
  /-- Every decoded fiber is duplicate-free — an explicit enumeration, not a multiset. -/
  fiber_nodup : ∀ n c, fibers.MapsTo n c → (decodeSeq c).Nodup
  /-- Every decoded fiber is nonempty. -/
  fiber_nonempty : ∀ n c, fibers.MapsTo n c → decodeSeq c ≠ []
  /-- Bonding maps each element of the next fiber into the previous fiber. -/
  bonding_mem : ∀ n c c' x y, fibers.MapsTo (n + 1) c → fibers.MapsTo n c' →
    x ∈ decodeSeq c → bonding.MapsTo (Nat.pair n x) y → y ∈ decodeSeq c'

/-- `s` is a section of the system: an internal graph-coded function choosing, at every
level, an element of that level's fiber, coherently under the bonding maps. Relational
throughout. -/
def InternalInverseSystem.IsSection {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (s : InternalFunction Ω) : Prop :=
  (∀ n c v, F.fibers.MapsTo n c → s.MapsTo n v → v ∈ decodeSeq c) ∧
    ∀ n v v', s.MapsTo (n + 1) v → s.MapsTo n v' → F.bonding.MapsTo (Nat.pair n v) v'

/-- The system has an internal section. -/
def InternalInverseSystem.HasSection {Ω : OmegaPart} (F : InternalInverseSystem Ω) : Prop :=
  ∃ s : InternalFunction Ω, F.IsSection s

/-- Explicit finite inverse-limit compactness at a second-order part: every internally
presented explicit finite inverse system has an internal section. No base-theory premise
inside the capability. -/
def EFILCAt (Ω : OmegaPart) : Prop :=
  ∀ F : InternalInverseSystem Ω, F.HasSection

end ReverseMathlib.Omega
