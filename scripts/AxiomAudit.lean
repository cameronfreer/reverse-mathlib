/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib

/-!
# Axiom audit

Checks that the library depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Run via `lake env lean scripts/AxiomAudit.lean`
(done by CI); any disallowed axiom is a hard error.

Two layers:

* **Environment sweep**: every declaration whose *owning module* is `ReverseMathlib` or
  a submodule is checked — including `private` declarations (whose mangled `_private.*`
  names defeat any namespace-prefix filter) and compiler-generated auxiliaries — so a
  `native_decide`/`ofReduceBool` (or any custom axiom) anywhere in the library fails the
  gate, whether or not the declaration is listed below.
* **Headline regression list**: `headlineDecls` is extended in every milestone; because
  the double-backtick names resolve at elaboration, a deletion or rename of a headline
  declaration also fails the gate.

The sweep only sees modules reachable from `ReverseMathlib`, i.e. the root import spine.
`ReverseMathlibExperimental.*` is deliberately outside it (see
`scripts/check_sorry_boundary.py`), so work in progress is not audited until it is
promoted.
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Headline declarations to audit; extended with each milestone. -/
def headlineDecls : List Name :=
  [-- Scaffold
   ``ReverseMathlib.exists_prime_gt_ten,
   -- Hall walking slice: the relative factorization theorem
   ``ReverseMathlib.Slice.countableHall_of_finiteInverseLimitCompactness,
   -- Tree bridges: the ambient WKL ↔ EFILC factorizations
   ``ReverseMathlib.Slice.efilc_of_weakKonig,
   ``ReverseMathlib.Slice.weakKonig_of_efilc,
   -- The end-to-end classical chain
   ``ReverseMathlib.Classical.weakKonig,
   ``ReverseMathlib.Classical.explicitFiniteInverseLimitCompactness,
   ``ReverseMathlib.Classical.countableHall_nat,
   -- Q-track pilot: Kohlenbach Prop. 2.27 / Cor. 2.28 and the rational realizer
   ``ReverseMathlib.Quantitative.exists_metastable_le_bound,
   ``ReverseMathlib.Quantitative.finite_metastability,
   ``ReverseMathlib.Quantitative.findMetastable_isSome,
   ``ReverseMathlib.Quantitative.findMetastable_congr,
   -- WKLω slice 1: the join least upper bound and the recursive-set Turing ideal
   ``ReverseMathlib.Omega.joinSet_le,
   ``ReverseMathlib.Omega.recursivePart_isTuringIdeal]

#eval show CoreM Unit from do
  for t in headlineDecls do
    let axs ← collectAxioms t
    for a in axs do
      unless allowedAxioms.contains a do
        throwError "axiom audit: {t} depends on disallowed axiom {a}"
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut swept := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`ReverseMathlib).isPrefixOf moduleNames[idx.toNat]! then
        let axs ← collectAxioms name
        for a in axs do
          unless allowedAxioms.contains a do
            throwError "axiom audit (sweep): {name} depends on disallowed axiom {a}"
        swept := swept + 1
  IO.println
    s!"axiom audit: {headlineDecls.length} headline declaration(s) clean; swept {swept}"
