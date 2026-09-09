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
