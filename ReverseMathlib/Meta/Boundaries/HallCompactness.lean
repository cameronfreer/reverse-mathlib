/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Boundary
import ReverseMathlib.Slice.HallFromCompactness

/-!
# The Hall-from-compactness declaration boundary (issue #20, first tranche)

The boundary against which `Slice.countableHall_of_finiteInverseLimitCompactness` is
checked. A coarse, revision-pinned **policy** — what the fixture's total closure may
contain — never a certified weak background and never a claim about any object theory.

* Module prefixes: core and the general-purpose mathlib libraries the proof's arithmetic,
  list, finset, and order reasoning live in, plus the tactic scaffolding residues
  (`Mathlib.Lean`, `Mathlib.Tactic`) that `omega`/`decide` leave in proof terms.
* Exact modules: **`Mathlib.Combinatorics.Hall.Finite` is admitted deliberately** — the
  fixture reuses finite Hall rather than reinventing it, and that reuse is the point; the
  two capability-interface modules `Standard.Hall` and `Standard.InverseLimit` are admitted
  as the explicit hypotheses' homes; `Batteries.Logic` (`congr_arg`) is admitted exactly.
* Exact declarations: the fixture's own coded-transversal helpers, listed by name, never
  `ReverseMathlib.Slice` wholesale.
* Forbidden, preceding every allowance: the compactness boundary that mathlib's infinite
  Hall crosses (`nonempty_sections_of_finite_inverse_system`, `CofilteredSystem`), the
  infinite Hall theorem itself, the matching-selection scaffolding, topological Kőnig, and
  all of `Mathlib.Topology` and `Mathlib.CategoryTheory`.
-/

namespace ReverseMathlib.Meta.Boundaries

open ReverseMathlib.Meta

/-- The declaration boundary for the Hall walking slice's relative theorem. -/
def hallCompactnessBoundary : DeclBoundary where
  id := "hall.finiteInverseLimitCompactness.v1"
  allowedPrefixes :=
    [`Init, `Batteries.Data, `Batteries.Control, `Batteries.Tactic, `Batteries.Lean,
     `Mathlib.Data, `Mathlib.Order, `Mathlib.Logic, `Mathlib.Algebra, `Mathlib.Lean,
     `Mathlib.Tactic, `Mathlib.Util, `Mathlib.Control]
  allowedModules :=
    [`Mathlib.Combinatorics.Hall.Finite, `Batteries.Logic,
     `ReverseMathlib.Standard.Hall, `ReverseMathlib.Standard.InverseLimit]
  allowedDecls :=
    [``ReverseMathlib.Slice.candLists, ``ReverseMathlib.Slice.mem_candLists,
     ``ReverseMathlib.Slice.decodeList, ``ReverseMathlib.Slice.decodeList_encode,
     ``ReverseMathlib.Slice.decodeList_spec, ``ReverseMathlib.Slice.hallSystem,
     ``ReverseMathlib.Slice.levelFiber, ``ReverseMathlib.Slice.transversalLists,
     ``ReverseMathlib.Slice.mem_transversalLists,
     ``ReverseMathlib.Slice.take_mem_transversalLists,
     ``ReverseMathlib.Slice.transversalLists_nonempty]
  forbiddenPrefixes := [`Mathlib.Topology, `Mathlib.CategoryTheory]
  forbiddenModules := [`Mathlib.Combinatorics.Hall.Basic, `Mathlib.Order.KonigLemma]
  -- literal names: this module does not import the forbidden machinery; the checker
  -- verifies at check time that every named constant exists (a missing name fails closed)
  forbiddenDecls :=
    [`nonempty_sections_of_finite_inverse_system,
     `Finset.all_card_le_biUnion_card_iff_exists_injective,
     `hallMatchingsOn.nonempty, `hallMatchingsFunctor]

end ReverseMathlib.Meta.Boundaries
