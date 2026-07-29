/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Registry

/-!
# Axiom audit for the tooling root

The same standard-axiom policy as `scripts/AxiomAudit.lean`, applied to the tooling/registry
root: every declaration owned by `ReverseMathlib.Meta.*`, `ReverseMathlib.Ports.*`, or the
aggregate module `ReverseMathlib.Registry` itself must depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Run via `lake env lean scripts/MetaAxiomAudit.lean` (done
by CI); any disallowed axiom — in particular `Lean.ofReduceBool`/`Lean.trustCompiler` from
`native_decide` — is a hard error. There is no exemption mechanism: if tooling code trips this
audit, the tooling code gets fixed.

Kept separate from the mathematical audit so that the mathematical sweep stays interpretable
and a future backend never inherits the tooling by accident.
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Modules owned by the tooling root. -/
def auditedModule (n : Name) : Bool :=
  n == `ReverseMathlib.Registry
    || (`ReverseMathlib.Meta).isPrefixOf n
    || (`ReverseMathlib.Ports).isPrefixOf n

#eval show CoreM Unit from do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut swept := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if auditedModule moduleNames[idx.toNat]! then
        let axs ← collectAxioms name
        for a in axs do
          unless allowedAxioms.contains a do
            throwError "meta axiom audit: {name} depends on disallowed axiom {a}"
        swept := swept + 1
  IO.println s!"meta axiom audit: swept {swept} tooling declaration(s)"
