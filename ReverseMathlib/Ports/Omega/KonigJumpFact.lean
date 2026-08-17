/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.KonigLeftmostPath
import ReverseMathlib.Ports.Omega.Catalog
import ReverseMathlib.Ports.Omega.BoundedKonig
import ReverseMathlib.Ports.Omega.JumpClosureFact

/-!
# The eighth production ω fact: jump closureω → explicitly bounded Kőnigω
(issue #50, slice A)

The **atomic registration** of the leftmost-path slice: over every Turing ideal, a
jump-closed second-order part satisfies explicitly bounded Kőnig — the first certified
comparison edge between the jump family and the WKL circle. Both endpoint variants are
already registered (`jumpClosure.turingIdealClosure.turingIdealOmega` with the seventh
fact, `wkl.explicitlyBoundedTree.internalBoundFunction.turingIdealOmega` with the
fourth); this tranche adds only the implication and its certificate.

The verdict stays precisely scoped: a kernel-checked **upper** implication over every
Turing ideal. No converse and no separation is claimed — the strictness of the
comparison (an ω-model of WKL₀ that is not jump closed) stays a literature-backed
reading of the corpus-recorded low-basis claim (Hirst thesis §1.4, Theorem 1.6) and is
NOT certified here. With this edge certified, the atlas orders the jump family above
the WKL circle by the fact itself; the literature-band placement this replaces is
retired in the same tranche.

The route (gated in `scripts/MetaSmoke.lean`): the leftmost path of the input tree is
computable from the jump of the tree joined with its bound graph —
`frontier_recursiveIn_join` (the finite extension search as a depth recursion in the
join), `extendibleSet_le_jump` (dead ends semidecidable, so extendibility is one
curry-coded jump query), `le_jump` (the base recovered through its own jump, never a
silent second oracle), and `leftmostExec_eq` (the executable recursion meets the
`leastChild` specification exactly under the extendibility invariant) — then internal
packaging by ideal closure alone.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

/-- **The ω-model implication certificate**: over every Turing ideal, jump closure gives
explicitly bounded Kőnig. Visibly the named direction theorem
`boundedKonigAt_of_jumpClosedAt` and nothing else; the dependency gates in
`scripts/MetaSmoke.lean` require this proof to reach the leftmost-path route spine, so
registration preserves the route artifact rather than replacing it with an inline
proof. -/
theorem jumpClosure_boundedKonig_omega_implication :
    Meta.SemanticImplicationCertificate IsTuringIdeal JumpClosedAt BoundedKonigAt :=
  ⟨fun _ h hj => boundedKonigAt_of_jumpClosedAt h hj⟩

rm_fact jumpClosureBoundedKonigOmega implication where
  base := rca0
  scope := omegaModels
  lhs := [jumpClosure.turingIdealClosure.turingIdealOmega]
  rhs := [wkl.explicitlyBoundedTree.internalBoundFunction.turingIdealOmega]
  note := "Over every Turing ideal, jump closure gives explicitly bounded Kőnig: the \
    leftmost path of an internally presented explicitly bounded tree is computable \
    from the jump of the tree joined with its bound graph. An upper implication only — \
    the first certified comparison edge between the jump family and the WKL circle. \
    The strictness of the comparison (an ω-model of WKL₀ that is not jump closed) \
    stays a literature-backed reading of the corpus-recorded low-basis claim (Hirst \
    thesis §1.4, Theorem 1.6) and is not certified here; no separation is claimed"

revmath_certify_fact jumpClosureBoundedKonigOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.jumpClosure_boundedKonig_omega_implication
  note := "The named direction theorem boundedKonigAt_of_jumpClosedAt, through the \
    leftmost-path route spine: frontier_recursiveIn_join, extendibleSet_le_jump, \
    le_jump, and leftmostExec_eq, then ideal closure. The route and this composition \
    are pinned by dependency gates in scripts/MetaSmoke.lean, including the \
    independence of le_jump from range_le_jump"

end ReverseMathlib.Ports
