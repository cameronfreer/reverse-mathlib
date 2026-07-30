/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Computability

/-!
# Internal sets (issue #22, slice 2)

The model-facing subtype: a set together with its membership witness in a second-order part.
**All model-facing outputs use this subtype** — the type system, not dependency analysis,
prevents ambient comprehension from manufacturing internal data. Raw `Set ℕ` remains useful
only inside reductions proving membership.
-/

namespace ReverseMathlib.Omega

/-- An internal set of a second-order part. -/
abbrev OmegaPart.InternalSet (Ω : OmegaPart) := {A : Set ℕ // A ∈ Ω}

/-- Internal membership of a natural in an internal set. -/
instance (Ω : OmegaPart) : Membership ℕ Ω.InternalSet := ⟨fun A n => n ∈ A.1⟩

/-- Closure transported to internal sets: anything reducible to an internal set is itself
realizable as an internal set. -/
def IsTuringIdeal.internalOfReducible {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (B : Ω.InternalSet) {A : Set ℕ} (hAB : A ≤ᵀ B.1) : Ω.InternalSet :=
  ⟨A, h.mem_of_reducible B.2 hAB⟩

/-- The join of two internal sets is internal. -/
def IsTuringIdeal.internalJoin {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (A B : Ω.InternalSet) : Ω.InternalSet :=
  ⟨joinSet A.1 B.1, h.join A.2 B.2⟩

/-- Every recursive set is realizable as an internal set of any Turing ideal. -/
def IsTuringIdeal.internalOfRecursive {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    {A : Set ℕ} (hA : RecursiveSet A) : Ω.InternalSet :=
  ⟨A, h.mem_of_recursive hA⟩

end ReverseMathlib.Omega
