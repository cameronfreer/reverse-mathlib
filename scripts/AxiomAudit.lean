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
   ``ReverseMathlib.Omega.recursivePart_isTuringIdeal,
   -- WKLω slice 3: the first completed bridge direction
   ``ReverseMathlib.Omega.weakKonigAt_of_efilcAt,
   -- WKLω slice 3: the compiled tree is computable from the system oracle
   ``ReverseMathlib.Omega.systemTreeSet_le_systemOracle,
   -- WKLω slice 3: the decoder reduces to fiber graph ⊕ path — the fine dependency
   ``ReverseMathlib.Omega.pathSectionGraph_le_join,
   -- Hall ω slice 4: the compiled matching fibers reduce to the enumerator alone
   ``ReverseMathlib.Omega.hallFiberGraph_le_enum,
   -- Hall ω slice 4: the completed direction
   ``ReverseMathlib.Omega.countableHallAt_of_efilcAt,
   -- Tranche 4: the Kleene tree — recursive membership, the diagonal, the countermodel
   ``ReverseMathlib.Omega.recursiveSet_kleeneTree,
   ``ReverseMathlib.Omega.not_isBinaryPathThrough_of_recursiveSet,
   ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart,
   -- Bounded Kőnig slice 3: fiber graph reduces to tree ⊕ bound; path to the section
   ``ReverseMathlib.Omega.boundedFiberGraph_le_join,
   ``ReverseMathlib.Omega.sectionBoundedPathGraph_le_graph,
   -- Bounded Kőnig slice 4: both genuine directions (the converse composes through EFILC)
   ``ReverseMathlib.Omega.boundedKonigAt_of_efilcAt,
   ``ReverseMathlib.Omega.weakKonigAt_of_boundedKonigAt,
   -- Matching slice 2: fiber graph reduces to enumerator ⊕ enumerator; matching to the
   -- section; the completed forward direction
   ``ReverseMathlib.Omega.mateFiberGraph_le_join,
   ``ReverseMathlib.Omega.sectionMatchingGraph_le_graph,
   ``ReverseMathlib.Omega.twoRegularPerfectMatchingAt_of_efilcAt,
   -- Matching slice 4: the gadget's three data reductions, the four-query separator,
   -- and the reversal's first leg (matching ⇒ disjoint-range separation)
   ``ReverseMathlib.Omega.SeparationGadget.gadgetEdges_le_join,
   ``ReverseMathlib.Omega.SeparationGadget.gadgetLeftGraph_le_join,
   ``ReverseMathlib.Omega.SeparationGadget.gadgetRightGraph_le_join,
   ``ReverseMathlib.Omega.SeparationGadget.separatorSet_le_graph,
   ``ReverseMathlib.Omega.matching_separates,
   -- Matching slice 5: the tree-to-injections reductions, the path decoder, and the
   -- reversal's second leg (separation ⇒ WKL)
   ``ReverseMathlib.Omega.TreeSeparation.fGraph_le_tree,
   ``ReverseMathlib.Omega.TreeSeparation.gGraph_le_tree,
   ``ReverseMathlib.Omega.TreeSeparation.pathSet_le_sep,
   ``ReverseMathlib.Omega.weakKonigAt_of_disjointRangeSeparationAt,
   -- Kőnig slice A (#50): the self-jump reduction, the frontier computation in the
   -- joined base oracle, the one-query extendibility decision, the leftmost-path
   -- graph reduction, and the packaged direction theorem
   ``ReverseMathlib.Omega.le_jump,
   ``ReverseMathlib.Omega.frontier_recursiveIn_join,
   ``ReverseMathlib.Omega.extendibleSet_le_jump,
   ``ReverseMathlib.Omega.leftmostGraph_le_jump,
   ``ReverseMathlib.Omega.boundedKonigAt_of_jumpClosedAt,
   -- Kőnig slice B (#50): the level-bound reduction, the injection tree's internality
   -- and path correctness, the complemented range decoder, and the three named theorems
   ``ReverseMathlib.Omega.levelBoundGraph_le_jump,
   ``ReverseMathlib.Omega.finitelyBranchingKonigAt_of_jumpClosedAt,
   ``ReverseMathlib.Omega.injectionTree_le_graph,
   ``ReverseMathlib.Omega.path_determines_range,
   ``ReverseMathlib.Omega.notMapsToZero_le_graph,
   ``ReverseMathlib.Omega.injectionRangeExistenceAt_of_finitelyBranchingKonigAt,
   ``ReverseMathlib.Omega.jumpClosedAt_of_finitelyBranchingKonigAt]

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
