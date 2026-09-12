/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Topology.Basic
import ReverseMathlib.Meta.Boundaries.HallCompactness

/-!
# Boundary-checker probes (issue #20, first tranche)

Declarations the boundary checker must reject or accept, each of a pinned shape. This
module deliberately imports `Mathlib.Topology.Basic`, a forbidden prefix, and
`Mathlib.Combinatorics.Hall.Basic`, a forbidden module: an **unused** forbidden import is
not a dependency (`probeClean` must pass) — import restrictions belong to the replay runner,
declaration restrictions to this checker. Not part of the library rollup; consumed by
`scripts/MetaSmoke.lean` only.
-/

namespace ReverseMathlibFixtures

open ReverseMathlib.Meta ReverseMathlib.Meta.Boundaries

/-- Reaches the compactness boundary (forbidden by name). -/
theorem probeCompactness : True := by
  have := @nonempty_sections_of_finite_inverse_system.{0, 0}
  trivial

/-- Reaches mathlib's infinite Hall theorem (forbidden by name and by module). -/
theorem probeInfiniteHall : True := by
  have := @Finset.all_card_le_biUnion_card_iff_exists_injective.{0, 0}
  trivial

/-- Reaches a topology declaration (forbidden by prefix, not by name). -/
theorem probeTopology : True := by
  have := @IsOpen.{0}
  trivial

/-- A statement wrapper around a forbidden declaration. -/
def wrapTopology : Prop := @IsOpen.{0} = @IsOpen.{0}

/-- A forbidden dependency shared by statement and proof, through the wrapper: absent from
the proof-only difference, present in the total closure. -/
theorem probeShared : wrapTopology := rfl

/-- An "allowed helper" whose body reaches a forbidden constant. -/
def helperHidden : Nat := by
  have := @IsOpen.{0}
  exact 0

/-- Depends on the forbidden constant only beneath the allowed helper. -/
def probeBeneathHelper : Nat := helperHidden

/-- Clean: uses nothing forbidden, in a module with forbidden imports. -/
theorem probeClean : (1 : Nat) + 1 = 2 := rfl

/-! ### Review probes: auxiliary spelling, the root, and the axiom policy -/

/-- An allowed helper. -/
def allowedHelper : Nat := 0

/-- Hand-written declarations whose names merely look like compiler-generated auxiliaries
of `allowedHelper`; they must not be admitted by spelling. -/
def allowedHelper._handwritten : Nat := 42
def allowedHelper.eq_handwritten : Nat := 17

/-- Depends only on the hand-written look-alikes. -/
def usesPretendAux : Nat := allowedHelper._handwritten + allowedHelper.eq_handwritten

/-- A custom axiom, present ONLY so the checker's independent standard-axiom policy has
something to reject. Never imported by any production root (this is the fixtures
library); the production axiom audit sweeps the root spines and cannot see it. -/
axiom addedAxiom : False

/-- Uses the custom axiom. -/
theorem fromAddedAxiom : False := addedAxiom

/-- A clean root, to be forbidden by name. -/
theorem cleanRoot : True := True.intro

/-- Only `allowedHelper` allowed (plus `Init`): the look-alikes must be rejected. -/
def boundaryNarrow : DeclBoundary :=
  { id := "probe.narrow", allowedPrefixes := [`Init], allowedDecls := [``allowedHelper] }

/-- The custom axiom explicitly allowed: the axiom policy must still reject it. -/
def boundaryAllowsAxiom : DeclBoundary :=
  { id := "probe.allowsAxiom", allowedPrefixes := [`Init],
    allowedDecls := [``addedAxiom, ``fromAddedAxiom] }

/-- Roots forbidden by name. -/
def boundaryForbiddenRoot : DeclBoundary :=
  { id := "probe.forbiddenRoot", allowedPrefixes := [`Init],
    forbiddenDecls := [``cleanRoot, ``addedAxiom] }

/-! ### Statement-agreement probes: binder info and binder names are part of the contract -/

theorem explicitInput (n : Nat) : n = n := rfl
theorem implicitInput {n : Nat} : n = n := rfl
theorem renamedInput (m : Nat) : m = m := rfl
theorem explicitInputAgain (n : Nat) : n = n := rfl

/-- The Hall boundary with the finite-Hall module removed: the genuine fixture must fail. -/
def boundaryNoFiniteHall : DeclBoundary :=
  { hallCompactnessBoundary with
      id := "probe.noFiniteHall",
      allowedModules := hallCompactnessBoundary.allowedModules.filter
        (· != `Mathlib.Combinatorics.Hall.Finite) }

/-- The Hall boundary plus `helperHidden` as an allowed declaration and the probes'
module admitted: allowances are not frontier cuts. -/
def boundaryAllowsHelper : DeclBoundary :=
  { hallCompactnessBoundary with
      id := "probe.allowsHelper",
      allowedDecls := ``helperHidden :: hallCompactnessBoundary.allowedDecls }

/-- The Hall boundary naming a constant that does not exist. -/
def boundaryMissingName : DeclBoundary :=
  { hallCompactnessBoundary with
      id := "probe.missingName",
      allowedDecls := `ReverseMathlib.Slice.thisDoesNotExist ::
        hallCompactnessBoundary.allowedDecls }

/-- The Hall boundary with the probes' module admitted (for `probeClean`). -/
def boundaryWithProbes : DeclBoundary :=
  { hallCompactnessBoundary with
      id := "probe.withProbes",
      allowedModules := `ReverseMathlibFixtures.BoundaryProbes ::
        hallCompactnessBoundary.allowedModules }

end ReverseMathlibFixtures
