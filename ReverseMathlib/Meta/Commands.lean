/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Report

/-!
# Dependency-audit commands

* `#rm_deps thm` — the complete dependency closure of `thm`: statement closure, value closure,
  proof-only closure, direct edges, kernel axioms, unknowns. **Never** cut: the raw closure is
  invariant under frontier registration by construction. `#rm_deps thm json` emits the
  machine-readable report.
* `#rm_frontier thm` — the same mining with traversal stopped at registered frontier
  declarations; the cut points actually reached are reported.
* `@[rm_frontier]` — label attribute registering a declaration as a frontier stopping point.
  Label attributes support tagging *imported* declarations after the fact:
  `attribute [rm_frontier] Some.Imported.decl`.
* Hard assertion commands, for CI gates rather than golden text. **All assertions require a
  complete (untruncated) closure and fail otherwise** — an absent dependency beyond the
  traversal limit must never pass a negative assertion. The closure inspected is explicit in
  each name:
  * `#rm_assert_depends thm dep` — `dep` is in the total closure (statement ∪ value);
  * `#rm_assert_proof_depends thm dep` — `dep` is in the proof-only closure;
  * `#rm_assert_not_proof_depends thm [dep₁, dep₂, …]` — no `depᵢ` is in the proof-only
    closure.

The visit bound is the `rm.maxNodes` option; truncated reports print `INCOMPLETE`.

**What the assertion gates certify, precisely.** Three distinct levels, in increasing
strength: (1) a *typed implication/factorization* — a relative theorem's statement, checked by
the kernel, says the conclusion follows from the named hypothesis; (2) *exclusion of known
alternate routes* — `#rm_assert_not_proof_depends` establishes only that the proof term does
not transitively invoke the *named* declarations; binder use is not a declaration edge, and an
ambient proof could in principle reconstruct a result by an unlisted route, so a negative gate
is evidence about the listed constants, never a proof that the hypothesis is logically
necessary; (3) *restricted replay or occurrence-level auditing* — the stronger future
certificate, not yet implemented. The walking-slice gates combine (1) and (2).
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

register_option rm.maxNodes : Nat := {
  defValue := 500000
  descr := "maximum constants visited per closure computation in #rm_deps/#rm_frontier/\
    #rm_assert_* (truncated results are INCOMPLETE and fail hard assertions)"
}

/-- Frontier stopping points for `#rm_frontier`: proof boundaries at which cut traversal stops.
Registration is honest labelling only — it never affects `#rm_deps` and carries no strength
claim. Apply to imported declarations with `attribute [rm_frontier] Some.decl`. -/
register_label_attr rm_frontier

/-- The `MineConfig` for the current options, with `stopAt` filled from the `rm_frontier` label
when `useFrontier` is set. -/
def mineConfig (useFrontier : Bool) : CommandElabM MineConfig := do
  let maxNodes := rm.maxNodes.get (← getOptions)
  let stopAt ← if useFrontier then
    let names ← liftCoreM <| labelled `rm_frontier
    pure <| names.foldl (init := ({} : NameSet)) fun s n => s.insert n
  else
    pure {}
  return { maxNodes, stopAt }

/-- Resolve a declaration name and mine it under the given configuration. -/
def mineForCommand (id : Ident) (useFrontier : Bool) : CommandElabM MineResult := do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let cfg ← mineConfig useFrontier
  match mineTarget (← getEnv) cfg target with
  | .ok r => return r
  | .error e => throwErrorAt id e

/-- Throw unless the mining result is complete. Every hard assertion goes through this gate:
truncated graphs prove nothing, in particular no absence. -/
def requireComplete (r : MineResult) : CommandElabM Unit := do
  if r.truncated then
    throwError "rm_assert: dependency closure of '{r.target}' is INCOMPLETE (truncated at \
      rm.maxNodes); raise the option — assertions never pass on a truncated graph"

/-- `#rm_deps thm`: the complete dependency closure of `thm` — never cut, invariant under
frontier registration. -/
elab "#rm_deps " id:ident : command => do
  let r ← mineForCommand id (useFrontier := false)
  logInfo (r.summary "#rm_deps")

/-- `#rm_deps thm json`: the machine-readable report, recording Lean version and mathlib
revision. (`json` is a soft keyword: it stays usable as an ordinary identifier elsewhere.) -/
elab "#rm_deps " id:ident &"json" : command => do
  let r ← mineForCommand id (useFrontier := false)
  let rev? ← readMathlibRev
  logInfo (toString (r.toJson rev?))

/-- `#rm_frontier thm`: mine with traversal stopped at `@[rm_frontier]`-labelled declarations. -/
elab "#rm_frontier " id:ident : command => do
  let r ← mineForCommand id (useFrontier := true)
  logInfo (r.summary "#rm_frontier")

/-- `#rm_assert_depends thm dep`: hard assertion that `dep` is in `thm`'s total closure
(statement ∪ value). Fails on a truncated graph. -/
elab "#rm_assert_depends " id:ident dep:ident : command => do
  let r ← mineForCommand id (useFrontier := false)
  requireComplete r
  let depName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo dep
  unless r.totalClosure.contains depName do
    throwErrorAt dep "rm_assert: '{r.target}' does not depend on '{depName}' \
      (total closure, complete)"

/-- `#rm_assert_proof_depends thm dep`: hard assertion that `dep` is in `thm`'s proof-only
closure (value closure minus statement closure). Fails on a truncated graph. -/
elab "#rm_assert_proof_depends " id:ident dep:ident : command => do
  let r ← mineForCommand id (useFrontier := false)
  requireComplete r
  let depName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo dep
  unless (r.proofOnlyClosure).contains depName do
    throwErrorAt dep "rm_assert: '{depName}' is not in the proof-only closure of '{r.target}' \
      (complete graph)"

/-- `#rm_assert_not_proof_depends thm [dep₁, …]`: hard assertion that none of the `depᵢ` are in
`thm`'s proof-only closure. Fails on a truncated graph, since absence cannot be concluded from
an incomplete traversal. -/
elab "#rm_assert_not_proof_depends " id:ident "[" deps:ident,* "]" : command => do
  let r ← mineForCommand id (useFrontier := false)
  requireComplete r
  let proofOnly := r.proofOnlyClosure
  for dep in deps.getElems do
    let depName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo dep
    if proofOnly.contains depName then
      throwErrorAt dep "rm_assert: forbidden dependency '{depName}' IS in the proof-only \
        closure of '{r.target}'"

end ReverseMathlib.Meta
