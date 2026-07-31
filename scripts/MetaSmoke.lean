/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.KonigLemma
import ReverseMathlib
import ReverseMathlib.Registry

/-!
# Meta smoke tests

Synthetic micro-tests for the dependency miner and hard-assertion commands, plus the Hall
walking slice's hard dependency gates, run in CI via `lake env lean scripts/MetaSmoke.lean`.
Semantic checks (`#eval` + `check` + `#rm_assert_*`) carry the invariants; `#guard_msgs`
goldens are kept compact and only cover command-level output shape.
-/

namespace RMSmoke

open Lean ReverseMathlib.Meta

/-- Fail with `msg` unless `b`. -/
def check (b : Bool) (msg : String) : CoreM Unit := do
  unless b do throwError "MetaSmoke: {msg}"

/-! ## Synthetic declaration graph -/

def base : Nat := 7

/-- Value-dependency on `base` only: the type mentions just `Nat`. -/
def valUser : Nat := base + 1

/-- Statement-dependency on `base`: the type mentions it. -/
def typeUser : Fin (base + 1) := ⟨0, Nat.succ_pos _⟩

/-- `valUser` occurs only in the proof, not the statement: a proof-only dependency. -/
theorem proofOnlyUser : True := (fun _ : valUser = valUser => True.intro) rfl

/-- `valUser` occurs in both statement and proof. -/
theorem bothUser : valUser = base + 1 := rfl

/-! Diamond: `d1 → d2 → base` and `d1 → d3 → base`. -/

def d2 : Nat := base
def d3 : Nat := base
def d1 : Nat := d2 + d3

/-- Reaches `base` only through `d2` — used to test that frontier cuts stop traversal. -/
def onlyThroughD2 : Nat := d2

/-- Inductive/constructor/recursor declaration group. -/
inductive Two where
  | a
  | b

/-- An opaque with a recorded body: not "unknown", and its value is traversed. -/
opaque opq : Nat := 5

def opqUser : Nat := opq

attribute [rm_frontier] d2

/-! ## Semantic checks on the mined graphs -/

#eval show CoreM Unit from do
  let env ← getEnv
  let cfg : MineConfig := {}
  -- Value-only vs type-only direct edges.
  let .ok r := mineTarget env cfg ``valUser | throwError "mine valUser failed"
  let some k := r.direct[``base]? | throwError "valUser has no direct edge to base"
  check (k.valueDep && !k.typeDep && !k.declarationGroupDep) "valUser → base must be value-only"
  let .ok r := mineTarget env cfg ``typeUser | throwError "mine typeUser failed"
  let some k := r.direct[``base]? | throwError "typeUser has no direct edge to base"
  check k.typeDep "typeUser → base must be a type dep"
  check (r.statement.reached.contains ``base) "base must be in typeUser's statement closure"
  -- Both-kinds edge.
  let .ok r := mineTarget env cfg ``bothUser | throwError "mine bothUser failed"
  let some k := r.direct[``valUser]? | throwError "bothUser has no direct edge to valUser"
  check (k.typeDep && k.valueDep) "bothUser → valUser must be both type and value"
  -- Proof-only closure.
  let .ok r := mineTarget env cfg ``proofOnlyUser | throwError "mine proofOnlyUser failed"
  check (r.proofOnlyClosure.contains ``valUser) "valUser must be proof-only for proofOnlyUser"
  check (!r.statement.reached.contains ``valUser) "valUser must not be in statement closure"
  -- Diamond: all nodes reached, both paths recorded, no duplicate-edge blowup.
  let .ok r := mineTarget env cfg ``d1 | throwError "mine d1 failed"
  for n in [``d2, ``d3, ``base] do
    check (r.value.reached.contains n) s!"{n} must be in d1's value closure"
  check ((r.state.graph.edges[``d2]?.bind (·[``base]?)).any (·.valueDep))
    "edge d2 → base must be recorded"
  check ((r.state.graph.edges[``d3]?.bind (·[``base]?)).any (·.valueDep))
    "edge d3 → base must be recorded"
  check (r.truncated == false) "d1 mining must be complete"

#eval show CoreM Unit from do
  let env ← getEnv
  let cfg : MineConfig := {}
  -- Declaration group: expected graph, not mere termination.
  let .ok r := mineTarget env cfg ``Two | throwError "mine Two failed"
  for c in [``Two.a, ``Two.b] do
    let some k := r.direct[c]? | throwError s!"Two has no group edge to {c}"
    check (k.declarationGroupDep && !k.typeDep && !k.valueDep)
      s!"Two → {c} must be a pure declaration-group edge"
    check (r.value.reached.contains c) s!"{c} must be in Two's value closure"
  -- Constructor → inductive arises as a typeDep, never synthesized as a group edge.
  check ((r.state.graph.edges[``Two.a]?.bind (·[``Two]?)).any
      fun k => k.typeDep && !k.declarationGroupDep)
    "Two.a → Two must be a type dep and not a group edge"
  -- Recursor: group edge to its inductive, merged with the type occurrence.
  let .ok r := mineTarget env cfg ``Two.rec | throwError "mine Two.rec failed"
  let some k := r.direct[``Two]? | throwError "Two.rec has no edge to Two"
  check (k.declarationGroupDep && k.typeDep) "Two.rec → Two must be group + type"
  check ((r.state.graph.nodes[``Two.rec]?).any (·.cls == .recDecl)) "Two.rec must classify recDecl"
  -- Opaque with recorded body: understood, value traversed, not unknown.
  let .ok r := mineTarget env cfg ``opqUser | throwError "mine opqUser failed"
  check ((r.state.graph.nodes[``opq]?).any (·.cls == .opaqueDecl)) "opq must classify opaqueDecl"
  check r.unknowns.isEmpty "opqUser closure must have no unknowns"
  -- Quot primitives are terminal and understood, not unknown.
  let .ok r := mineTarget env cfg ``Quot.mk | throwError "mine Quot.mk failed"
  check ((r.state.graph.nodes[``Quot.mk]?).any (·.cls == .quotPrimitive))
    "Quot.mk must classify quotPrimitive"
  check r.unknowns.isEmpty "Quot.mk closure must have no unknowns"
  -- Missing declaration is a hard error, not an empty result.
  match mineTarget env cfg (`RMSmoke ++ `doesNotExist) with
  | .error _ => pure ()
  | .ok _ => throwError "mining a nonexistent constant must fail"

#eval show CoreM Unit from do
  let env ← getEnv
  -- Frontier cut: base is reachable only through the cut point, so it must not be reached.
  let stopAt : NameSet := ({} : NameSet).insert ``d2
  let .ok r := mineTarget env { stopAt } ``onlyThroughD2 | throwError "mine cut failed"
  check (r.state.cuts.contains ``d2) "d2 must be recorded as a cut"
  check (r.value.reached.contains ``d2) "the cut point itself must be reached"
  check (!r.value.reached.contains ``base) "base must not be reached past the cut"
  -- Raw mining of the same target is invariant under frontier registration.
  let .ok raw := mineTarget env {} ``onlyThroughD2 | throwError "mine raw failed"
  check (raw.value.reached.contains ``base) "raw closure must pass through d2 to base"
  check (raw.state.cuts.isEmpty) "raw mining must record no cuts"
  -- Deterministic truncation: tiny budget must mark the result incomplete.
  let .ok r := mineTarget env { maxNodes := 2 } ``d1 | throwError "mine truncated failed"
  check r.truncated "maxNodes := 2 must truncate d1's closure"

/-! ## Command-level checks -/

/-- info: #rm_deps RMSmoke.proofOnlyUser
  kernel axioms: (none)
  statement closure: 2 constants
  value closure: 35 constants
  proof-only closure: 33 constants
  direct deps: 1 type / 5 value / 0 group (0 instances)
  top modules in proof-only closure: Init.Prelude (31), «<current file>» (2)
  unknown constants: (none)
-/
#guard_msgs in
#rm_deps proofOnlyUser

#guard_msgs in
#rm_assert_depends d1 base

#guard_msgs in
#rm_assert_proof_depends proofOnlyUser valUser

#guard_msgs in
#rm_assert_not_proof_depends d1 [typeUser, opq]

-- The frontier command reports the cut, and the cut stops traversal (base is absent).
/-- info: #rm_frontier RMSmoke.onlyThroughD2
  kernel axioms: (none)
  statement closure: 3 constants
  value closure: 1 constants
  proof-only closure: 1 constants
  direct deps: 1 type / 1 value / 0 group (0 instances)
  top modules in proof-only closure: «<current file>» (1)
  frontier cuts: RMSmoke.d2
  unknown constants: (none)
-/
#guard_msgs in
#rm_frontier onlyThroughD2

-- Assertions must fail, not silently pass, on truncated graphs.
/--
error: rm_assert: dependency closure of 'RMSmoke.d1' is INCOMPLETE (truncated at rm.maxNodes); raise the option — assertions never pass on a truncated graph
-/
#guard_msgs in
set_option rm.maxNodes 2 in
#rm_assert_not_proof_depends d1 [opq]

/-! ## The Hall walking slice: hard dependency gates

These are the milestone's semantic certificates, not demonstrations. Mathlib's infinite Hall
theorem factors through the topological compactness boundary and the `hallMatchingsOn`
matching-selection scaffolding; the relative theorem
`countableHall_of_finiteInverseLimitCompactness` reuses mathlib's *finite* Hall theorem but
factors through the `ExplicitFiniteInverseLimitCompactness` hypothesis instead — its proof-only
closure contains none of that machinery. All assertions require complete closures.

A limitation found while writing these gates, recorded honestly: `Classical.indefiniteDescription`
is **not** assertable at constant granularity. `Classical.em` is itself proved via
`Classical.choose`/`indefiniteDescription`, so every classical proof — including ours — reaches
the constant transitively, and it already sits in the *statement* closures through decidability
instance values. "Mathlib selects a matching with `Classical.indefiniteDescription` at
`Hall/Basic.lean:73` and our construction has no counterpart of that step" is an
*occurrence-level* fact, visible in source and recorded in the port record; occurrence-level
auditing is future work. The constant-level gates below instead target the specific mathlib
scaffolding that performs the selection. -/

-- The mined architecture: mathlib's infinite Hall proof crosses the compactness boundary
-- and the matching-selection scaffolding.
#rm_assert_proof_depends Finset.all_card_le_biUnion_card_iff_exists_injective
  nonempty_sections_of_finite_inverse_system

#rm_assert_proof_depends Finset.all_card_le_biUnion_card_iff_exists_injective
  hallMatchingsOn.nonempty

-- The relative proof reuses finite Hall — proof reuse, not reinvention.
#rm_assert_proof_depends ReverseMathlib.Slice.countableHall_of_finiteInverseLimitCompactness
  Finset.all_card_le_biUnion_card_iff_existsInjective'

-- The factorization certificate: the compactness boundary and the selection scaffolding
-- are absent from the relative proof.
#rm_assert_not_proof_depends ReverseMathlib.Slice.countableHall_of_finiteInverseLimitCompactness
  [Finset.all_card_le_biUnion_card_iff_exists_injective,
   nonempty_sections_of_finite_inverse_system,
   hallMatchingsFunctor,
   hallMatchingsOn.nonempty]

/-! ### Tree-bridge gates: the WKL ↔ EFILC factorizations

Both directions must factor through their hypotheses, not through mathlib's classical Kőnig
machinery (order-theoretic or topological) or the infinite Hall theorem. -/

#rm_assert_not_proof_depends ReverseMathlib.Slice.efilc_of_weakKonig
  [nonempty_sections_of_finite_inverse_system,
   exists_seq_forall_proj_of_forall_finite,
   Finset.all_card_le_biUnion_card_iff_exists_injective]

#rm_assert_not_proof_depends ReverseMathlib.Slice.weakKonig_of_efilc
  [nonempty_sections_of_finite_inverse_system,
   exists_seq_forall_proj_of_forall_finite,
   Finset.all_card_le_biUnion_card_iff_exists_injective]

/-! ### End-to-end classical chain gates

`Classical.weakKonig` is proved from mathlib's order-theoretic Kőnig lemma; everything below
is derived through the relative bridges. `countableHall_nat` must reach both bridges and
finite Hall, and never the infinite Hall theorem or the topological inverse-limit theorem. -/

#rm_assert_proof_depends ReverseMathlib.Classical.weakKonig
  exists_seq_forall_proj_of_forall_finite

#rm_assert_proof_depends ReverseMathlib.Classical.countableHall_nat
  ReverseMathlib.Slice.countableHall_of_finiteInverseLimitCompactness

#rm_assert_proof_depends ReverseMathlib.Classical.countableHall_nat
  ReverseMathlib.Slice.efilc_of_weakKonig

#rm_assert_proof_depends ReverseMathlib.Classical.countableHall_nat
  Finset.all_card_le_biUnion_card_iff_existsInjective'

#rm_assert_not_proof_depends ReverseMathlib.Classical.countableHall_nat
  [Finset.all_card_le_biUnion_card_iff_exists_injective,
   nonempty_sections_of_finite_inverse_system]

/-! ### ω-capability statement-burden gates (#22 slice 2)

The Turing-ideal capability statements are formulated relationally (`MapsTo`/membership):
their **capability-definition closures** (the value closure of each defining constant) must
never reach the choice-derived `InternalFunction.eval` — otherwise the exact variants would
silently acquire an explicit selection route. -/

#eval show CoreM Unit from do
  let env ← getEnv
  for t in [``ReverseMathlib.Omega.WeakKonigAt, ``ReverseMathlib.Omega.EFILCAt] do
    let .ok r := mineTarget env {} t | throwError "mine {t} failed"
    check (!r.truncated) s!"{t} capability-definition mining must be complete"
    check (!r.value.reached.contains ``ReverseMathlib.Omega.InternalFunction.eval)
      s!"{t} capability-definition closure must not reach InternalFunction.eval"
    -- Recorded honestly: `Classical.choice` IS reachable at constant granularity — through
    -- mathlib's Encodable/Denumerable instance chain for the sequence coding, not through
    -- any selection in the statements themselves (the same granularity limitation as the
    -- indefiniteDescription note above). The `eval` gate is the meaningful discipline: no
    -- choice-derived evaluation enters a capability statement.

/-! ### ω-bridge route gate (#22 slice 3)

`EFILCω → WKLω` must factor through the `treeToSystem`/`sectionToPath` route and reach
neither compiler of the opposite direction — the route certificate for the first completed
direction, checked as a proof-only closure fact. -/

#rm_assert_proof_depends ReverseMathlib.Omega.weakKonigAt_of_efilcAt
  ReverseMathlib.Omega.treeToSystem

#rm_assert_proof_depends ReverseMathlib.Omega.weakKonigAt_of_efilcAt
  ReverseMathlib.Omega.sectionPathInternal

#rm_assert_not_proof_depends ReverseMathlib.Omega.weakKonigAt_of_efilcAt
  [ReverseMathlib.Omega.systemTreeSet,
   ReverseMathlib.Omega.CoherentEncoding]

-- The compactness boundary is registered as a frontier declaration (an *imported* one) in
-- ReverseMathlib.Ports.Mathlib.Hall; here we check the cut it produces.
#eval show CoreM Unit from do
  let env ← getEnv
  let stopAt : NameSet := ({} : NameSet).insert ``nonempty_sections_of_finite_inverse_system
  let .ok r := mineTarget env { stopAt }
      ``Finset.all_card_le_biUnion_card_iff_exists_injective
    | throwError "mine mathlib Hall failed"
  check (r.state.cuts.contains ``nonempty_sections_of_finite_inverse_system)
    "the compactness boundary must appear as a frontier cut in mathlib's infinite Hall"

/-! ## Registry micro-tests

Fail-closed behavior of the evidence registry: duplicate ids rejected, a bogus certificate with
the wrong type rejected (a bare kernel-checked reference must not masquerade as a certificate),
ambient-Lean evidence cannot carry a semantic scope, and the Hall walking-slice port record
renders its honest verdict. -/

-- Production registry statistics: the state from imports alone, BEFORE the synthetic fixtures
-- below are registered. The fixture-inclusive statistic is pinned separately at the end.
/--
info: concepts: 3; variants: 5; ports: 2; evidence: 3 (3 kernel checked, 0 claimed, 0 backend checked); certified unique facts — ω-model: 0; all-model: 0; syntactic: 0
-/
#guard_msgs in
#revmath_stats

-- Catalog export: the production ambient-factorization graph has exactly the three
-- direction-aware edges. The easy endpoint bug — treating `assumes` as the source
-- unconditionally — would flip the lower edge; both orientations are pinned here.
#eval show CoreM Unit from do
  let env ← getEnv
  let snap := CatalogSnapshot.ofEnv env
  check (snap.ambientEdges.size == 3) "production ambient graph must have exactly 3 edges"
  let has (s t : Name) : Bool := snap.ambientEdges.any fun e => e.source == s && e.target == t
  check (has `ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness
      `ReverseMathlib.Standard.CountableHall) "upper: EFILC -> CountableHall"
  check (has `ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness
      `ReverseMathlib.Standard.WeakKonig) "upper: EFILC -> WeakKonig"
  check (has `ReverseMathlib.Standard.WeakKonig
      `ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness)
    "lower: WeakKonig -> EFILC (port statement is the source)"
  check (!has `ReverseMathlib.Standard.CountableHall
      `ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness)
    "no spurious reversed Hall edge"
  -- Migration golden: variants own the interfaces, edges keep Lean-declaration endpoints,
  -- and the exporter cross-links nodes to variants without changing graph identity.
  let cat := ConceptCatalog.ofEnv env
  let some v := cat.findVariant? `wkl.binaryTree.ambient
    | throwError "wkl.binaryTree.ambient must be registered"
  check (v.concept == ⟨`wkl⟩) "variant parent concept is explicit data"
  check (v.interface? == some `ReverseMathlib.Standard.WeakKonig)
    "variant owns the WeakKonig interface"
  check (cat.interfaceOwner[`ReverseMathlib.Standard.WeakKonig]? == some ⟨`wkl.binaryTree.ambient⟩)
    "interface ownership is indexed"
  -- Layer-indexed interface schemas (#5): the production ambient layer has no schema, so its
  -- Prop-only interface validation is byte-for-byte the pre-#5 behavior.
  check ((cat.layers.find? (·.id.name == `ambient)).any (·.interfaceSchema?.isNone))
    "the production ambient layer must carry no interface schema (Prop-only preserved)"
  -- ω-layer registration pins (#22 slice 2): base theory, layer schema, semantic context,
  -- and the exact interface owners. Certified counts stay 0/0/0 (stats goldens) and the
  -- ambient graph is untouched (3-edge pin above) — registration adds no evidence.
  check (cat.baseTheories.any (·.id.name == `rca0)) "rca0 base theory registered"
  check ((cat.layers.find? (·.id.name == `turingIdealOmega)).any
      (·.interfaceSchema? == some `ReverseMathlib.Ports.OmegaInterface))
    "turingIdealOmega layer carries the OmegaInterface schema"
  check ((cat.semanticContexts.find? (·.id.name == `rca0.turingIdealOmega)).any fun c =>
      c.base.name == `rca0 && c.scope == .omegaModels &&
        c.contextDecl == `ReverseMathlib.Omega.IsTuringIdeal)
    "rca0.turingIdealOmega context pins base, scope, and the IsTuringIdeal predicate"
  check (cat.interfaceOwner[`ReverseMathlib.Omega.WeakKonigAt]? ==
      some ⟨`wkl.binaryTree.turingIdealOmega⟩)
    "WeakKonigAt is owned by wkl.binaryTree.turingIdealOmega"
  check (cat.interfaceOwner[`ReverseMathlib.Omega.EFILCAt]? ==
      some ⟨`efilc.explicitSequential.enumeratedFibers.turingIdealOmega⟩)
    "EFILCAt is owned by efilc.explicitSequential.enumeratedFibers.turingIdealOmega"

/-! ### Conceptual catalog (production seed + acceptance tests)

Concept registration requires no Lean proposition; only exact aliases resolve; provenance
relations may legitimately appear on several targets; unknown namespaces and duplicates are
rejected; punctuated external keys survive. The cross-module collision tests (sibling modules
that only conflict when merged) live in the `ReverseMathlibFixtures` library. -/

/--
info: concepts (3):
  reverse-mathlib:countableHall — Countable Hall / marriage as a conceptual family: the one-sided injective-choice and perfect-matching (Simpson X.3.15/X.3.16) variants are related but not identical, and no RMZoo symbol exists for this family
    variant reverse-mathlib:countableHall.oneSidedInjective.ambient [ambient] ⟨ReverseMathlib.Standard.CountableHall⟩
    simpson:"X.3.15" [relatedVariant]
    simpson:"X.3.16" [relatedVariant]
  reverse-mathlib:explicitFiniteInverseLimitCompactness — Explicit finite inverse-limit compactness as a conceptual family: sequential systems of explicitly enumerated finite fibers with adjacent bonding maps
    variant reverse-mathlib:efilc.explicitSequential.ambient [ambient] ⟨ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness⟩
    variant reverse-mathlib:efilc.explicitSequential.enumeratedFibers.turingIdealOmega [turingIdealOmega] ⟨ReverseMathlib.Omega.EFILCAt⟩
  reverse-mathlib:wkl — Weak Kőnig's lemma as a conceptual family: binary-tree formulations across semantic layers (ambient / ω-model / second-order syntax); explicitly bounded formulations may join once their relationship is fixed. Merely finitely branching (full Kőnig) is the ACA-level principle and belongs to a separate concept, not under the rmzoo:WKL alias
    variant reverse-mathlib:wkl.binaryTree.ambient [ambient] ⟨ReverseMathlib.Standard.WeakKonig⟩
    variant reverse-mathlib:wkl.binaryTree.turingIdealOmega [turingIdealOmega] ⟨ReverseMathlib.Omega.WeakKonigAt⟩
    concordance:"C085" [importedCorrespondence]
    rmzoo:"WKL" [exactAlias]
    simpson:"I.10" [sourceLocation]
namespaces (4):
  concordance — reverse_mathematics_concordance.xlsx row identifiers — external provenance, never canonical identity
  rmzoo — Reverse Mathematics Zoo symbols (github.com/ericastor/rmzoo, pinned import arrives with issue #7)
  sanders — [San] Sam Sanders, Reverse Mathematics: there and back again, monograph under review with Springer, pp 450, 2026 — references
  simpson — [Sim09] Simpson, Subsystems of Second Order Arithmetic, 2nd ed. — section and theorem references
-/
#guard_msgs in
#rm_concepts

/-- info: rmzoo:"WKL" = reverse-mathlib:wkl -/
#guard_msgs in
#rm_resolve rmzoo "WKL"

-- Provenance relations never resolve.
/--
error: concept catalog: no exact alias for simpson:"I.10" (provenance relations do not resolve)
-/
#guard_msgs in
#rm_resolve simpson "I.10"

-- Same-module duplicates and unknown namespaces are rejected at registration.
/-- error: concept catalog: duplicate concept id 'wkl' -/
#guard_msgs in
rm_concept wkl where
  description := "duplicate"

/--
error: concept catalog: namespace 'nosuchns' is not registered (rm_namespace first; namespaces are extensible by registration)
-/
#guard_msgs in
rm_external_ref nosuchns "K" exactAlias concept wkl

/-- error: concept catalog: unknown concept 'nosuchconcept' -/
#guard_msgs in
rm_external_ref rmzoo "K2" exactAlias concept nosuchconcept

/--
error: concept catalog: exact alias rmzoo:"WKL" already resolves to 'wkl'
-/
#guard_msgs in
rm_external_ref rmzoo "WKL" exactAlias concept countableHall

-- Statement targets must reference registered variants.
/-- error: concept catalog: unknown statement variant 'wkl' -/
#guard_msgs in
rm_external_ref rmzoo "K3" exactAlias statement wkl

-- A sourceLocation may legitimately appear on several targets; punctuated keys round-trip.
rm_namespace fixdoi "fixture namespace for punctuation round-trip"
rm_external_ref fixdoi "10.1017/jsl.2020.68(a)+x" exactAlias concept wkl
rm_external_ref simpson "X.3" sourceLocation concept wkl
rm_external_ref simpson "X.3" sourceLocation concept countableHall

/-- info: fixdoi:"10.1017/jsl.2020.68(a)+x" = reverse-mathlib:wkl -/
#guard_msgs in
#rm_resolve fixdoi "10.1017/jsl.2020.68(a)+x"

#eval show CoreM Unit from do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  check cat.conflicts.isEmpty "repeated sourceLocation on two targets must not conflict"
  check (cat.aliasMap[(`simpson, "X.3")]?.isNone) "sourceLocation never enters the alias map"
  check (cat.aliasMap[(`rmzoo, "WKL")]?.isSome) "exact alias present in the alias map"

def smokeProp : Prop := True
def otherProp : Prop := (2 : ℕ) = 2

/-- A kernel-checked theorem of certificate *shape* but the wrong *type*: its assumption is not
the registered interface of the principle it will claim to assume. -/
theorem bogusCert : ReverseMathlib.Meta.RelativeCertificate ((1 : ℕ) = 1) smokeProp :=
  ⟨fun _ => trivial⟩

rm_concept smokeConcept where
  description := "fixture concept for registry tests"

rm_statement_variant smokeVariant where
  concept := smokeConcept
  layer := ambient
  interface := RMSmoke.otherProp
  description := "fixture capability variant (interface otherProp)"

rm_statement_variant smokePropVariant where
  concept := smokeConcept
  layer := ambient
  interface := RMSmoke.smokeProp
  description := "fixture target variant (interface smokeProp)"

/-- error: concept catalog: duplicate statement-variant id 'smokeVariant' -/
#guard_msgs in
rm_statement_variant smokeVariant where
  concept := smokeConcept
  layer := ambient
  description := "duplicate"

/--
error: registry: certificate 'RMSmoke.bogusCert' assumes '1 =
  1', which is not definitionally the registered interface 'RMSmoke.otherProp' of the cited principle
-/
#guard_msgs in
revmath_port bogusPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof upper kernelChecked lean
    via RMSmoke.bogusCert
    assumes smokeVariant

/--
error: registry: ambient-Lean evidence carries no RM semantic scope; remove the scope or change the ambient
-/
#guard_msgs in
revmath_port scopedPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof upper claimed lean scope omegaModels

/-- error: registry: duplicate port id 'countableHall' -/
#guard_msgs in
revmath_port countableHall where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue

/-! ### Hardening: typed, direction-aware, scope-preserving certificates -/

-- Kernel-checked semantic/syntactic evidence is rejected until typed schemas exist: an axiom
-- audit alone certifies nothing — pinned with the literal `True.intro`.
/--
error: registry: semanticImplication evidence must name the assumed statement variant (assumes ...), even when merely claimed
-/
#guard_msgs in
revmath_port semanticPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    via True.intro

-- Evidence kind and ambient must agree.
/--
error: registry: evidence kind 'ReverseMathlib.Meta.EvidenceKind.relativeProof' requires ambient 'ReverseMathlib.Meta.ProofAmbient.lean', got 'ReverseMathlib.Meta.ProofAmbient.modelSemantics'
-/
#guard_msgs in
revmath_port mismatchPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof upper claimed modelSemantics scope omegaModels

/-- A `P → T` certificate: acceptable only as *upper* evidence. -/
theorem upperShapedCert : ReverseMathlib.Meta.RelativeCertificate RMSmoke.otherProp
    RMSmoke.smokeProp := ⟨fun _ => trivial⟩

-- Direction-aware matching: an upper-shaped certificate is rejected as lower evidence.
/--
error: registry: certificate 'RMSmoke.upperShapedCert' assumes 'otherProp', which is not definitionally the registered port statement 'RMSmoke.smokeProp' of the cited principle
-/
#guard_msgs in
revmath_port wrongDirPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof lower kernelChecked lean
    via RMSmoke.upperShapedCert
    assumes smokeVariant

/-- A correctly-shaped *lower* certificate: `T → P` (port statement implies interface). -/
theorem lowerShapedCert : ReverseMathlib.Meta.RelativeCertificate RMSmoke.smokeProp
    RMSmoke.otherProp := ⟨fun _ => rfl⟩

revmath_port lowerFixture where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof lower kernelChecked lean
    via RMSmoke.lowerShapedCert
    assumes smokeVariant
  evidence relativeProof lower claimed lean
    assumes smokeVariant

/-! ### Evidence-field compatibility matrix: malformed unverified records are rejected too -/

/--
error: registry: relativeProof evidence must name the assumed statement variant (assumes ...), even when merely claimed
-/
#guard_msgs in
revmath_port noAssumesPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof lower claimed lean

/-- error: registry: only relativeProof and semanticImplication evidence may carry assumes -/
#guard_msgs in
revmath_port strayAssumesPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence dependencyAudit upper claimed lean
    assumes smokeVariant

/--
error: registry: syntacticDerivation evidence must name its object theory (theory ...), through the dedicated field rather than the scope
-/
#guard_msgs in
revmath_port noTheoryPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence syntacticDerivation upper claimed objectTheory

/--
error: registry: via citations are only for kernelChecked evidence; cite literature in the note
-/
#guard_msgs in
revmath_port strayViaPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof lower claimed lean
    via RMSmoke.bogusCert
    assumes smokeVariant

-- An ambient lower factorization (and a fortiori a claimed lower record) is NOT an RM lower
-- bound: both pending lines must survive.
/--
info: lowerFixture
  mathlib: RMSmoke.smokeProp
  target: reverse-mathlib:smokePropVariant
  port: RMSmoke.smokeProp
  source relation: conceptual analogue
  lower · relative Lean factorization: kernel checked
    certificate: RMSmoke.lowerShapedCert (assumes smokeVariant)
    ambient: unrestricted Lean over standard ℕ; RM semantic scope: none
  lower · relative Lean factorization: claimed (UNVERIFIED)
    ambient: unrestricted Lean over standard ℕ; RM semantic scope: none
  candidate classical classification: unknown
  backend RM certificate: pending
  exact lower bound: pending
-/
#guard_msgs in
#revmath_port? lowerFixture

-- The fixture's lower certificate exports with the port statement as the SOURCE.
#eval show CoreM Unit from do
  let env ← getEnv
  let snap := CatalogSnapshot.ofEnv env
  check (snap.ambientEdges.any fun e =>
      e.source == `RMSmoke.smokeProp && e.target == `RMSmoke.otherProp &&
        e.direction == .lower)
    "fixture lower edge must map port statement -> principle interface"

-- The walking slice's honest verdict, pinned.
/--
info: countableHall
  mathlib: Finset.all_card_le_biUnion_card_iff_exists_injective
  target: reverse-mathlib:countableHall.oneSidedInjective.ambient
  port: ReverseMathlib.Standard.CountableHall
  source relation: proof analogue / mined architecture
  upper · relative Lean factorization: kernel checked
    certificate: ReverseMathlib.Ports.countableHallRelativeCertificate (assumes efilc.explicitSequential.ambient)
    ambient: unrestricted Lean over standard ℕ; RM semantic scope: none
    note: Proof-only closure certified by CI (scripts/MetaSmoke.lean): contains finite Hall, excludes the infinite Hall theorem, the compactness boundary, and the selection scaffolding.
  candidate classical classification: future internally coded/model-relative analogue: WKL₀ candidate; the current ambient one-sided injective-choice variant has no certified RM classification; relationship to Simpson X.3.15/X.3.16: related statement variant, not identical [claimed, UNVERIFIED]
  backend RM certificate: pending
  exact lower bound: pending
  note: Mined from mathlib's proof: finite Hall reused for level nonemptiness; the topological compactness boundary (nonempty_sections_of_finite_inverse_system, ultimately Tychonoff) and the hallMatchingsOn selection scaffolding replaced by the EFILC hypothesis over explicitly enumerated Finset fibers — no Nonempty-instance extraction step remains (occurrence-level fact; see scripts/MetaSmoke.lean for the constant-level gates and the recorded indefiniteDescription granularity limitation).
-/
#guard_msgs in
#revmath_port? countableHall

/--
info: concepts: 4; variants: 7; ports: 3; evidence: 5 (4 kernel checked, 1 claimed, 0 backend checked); certified unique facts — ω-model: 0; all-model: 0; syntactic: 0
-/
#guard_msgs in
#revmath_stats

/-! ### Typed facts and contexts (#5)

Conjunction ASTs normalize (permuted duplicates collide); base theory, fact scope, and
statement layer stay distinct (the same statement at another scope is another fact); RM and
uniform fact families never mix; endpoints are exact statement variants or exact uniform
problems, never concepts; rendering is fail-closed — recorded, no evidence linked. -/

#eval show CoreM Unit from do
  let a : StatementVariantId := ⟨`aVar⟩
  let b : StatementVariantId := ⟨`bVar⟩
  check (VariantConjunction.normalize #[b, a, a] == VariantConjunction.normalize #[a, b])
    "conjunction normalization must sort and deduplicate"
  check ((VariantConjunction.normalize #[b, a, a]).serialized == "aVar+bVar")
    "canonical serialization is the normalized order"

rm_base_theory fixRca0 "fixture base theory"
rm_formula_class fixPi11 "fixture formula class"
rm_reducibility_notion fixWeihrauch "fixture reducibility notion"

rm_uniform_problem smokeProblemA where
  concept := smokeConcept
  input := "fixture input"
  output := "fixture output"
  operation := single

rm_uniform_problem smokeProblemB where
  concept := smokeConcept
  input := "fixture input"
  output := "fixture output"
  operation := sequentialization

-- An RM fact; the lhs conjunction arrives unnormalized.
rm_fact fixImp implication where
  base := fixRca0
  scope := provability
  lhs := [smokePropVariant, smokeVariant, smokeVariant]
  rhs := [smokePropVariant]

-- The same statement at a different scope is a DIFFERENT fact.
rm_fact fixImpOmega implication where
  base := fixRca0
  scope := omegaModels
  lhs := [smokeVariant, smokePropVariant]
  rhs := [smokePropVariant]

-- Duplicate content under a fresh id is rejected — normalization makes permuted duplicates
-- collide.
/--
error: concept catalog: duplicate fact content: this fact is already registered as 'fixImp' (conjunctions compare in normalized form)
-/
#guard_msgs in
rm_fact fixImpAgain implication where
  base := fixRca0
  scope := provability
  lhs := [smokeVariant, smokePropVariant]
  rhs := [smokePropVariant]

-- Endpoints are exact statement variants — a concept id is rejected, never coerced.
/--
error: concept catalog: unknown statement variant 'smokeConcept' — fact endpoints are exact statement variants, never concepts
-/
#guard_msgs in
rm_fact fixBadEndpoint implication where
  base := fixRca0
  scope := provability
  lhs := [smokeConcept]
  rhs := [smokePropVariant]

-- Cross-axis: RM kinds never take notion/status …
/--
error: concept catalog: RM fact kind 'implication' takes base/scope, not notion/status — the RM and uniform fact families never mix
-/
#guard_msgs in
rm_fact fixCrossA implication where
  notion := fixWeihrauch
  status := exact
  lhs := [smokeVariant]
  rhs := [smokePropVariant]

-- … and uniform kinds never take base/scope.
/--
error: concept catalog: uniform fact kind 'reducibility' takes notion/status, not base/scope — the RM and uniform fact families never mix
-/
#guard_msgs in
rm_fact fixCrossB reducibility where
  base := fixRca0
  scope := provability
  lhs := [smokeProblemA]
  rhs := [smokeProblemB]

-- Uniform endpoints are represented problems, never statement variants.
/--
error: concept catalog: unknown uniform problem 'smokeVariant' — uniform facts relate exact represented problems, never statement variants or concepts
-/
#guard_msgs in
rm_fact fixBadUniform reducibility where
  notion := fixWeihrauch
  status := exact
  lhs := [smokeVariant]
  rhs := [smokeProblemB]

-- A uniform fact with its mandatory degree status.
rm_fact fixRed reducibility where
  notion := fixWeihrauch
  status := representative
  lhs := [smokeProblemA]
  rhs := [smokeProblemB]

-- Conservation requires its formula class.
/-- error: concept catalog: conservation facts require formulaClass := … -/
#guard_msgs in
rm_fact fixConsMissing conservation where
  base := fixRca0
  scope := provability
  lhs := [smokeVariant]
  rhs := [smokePropVariant]

rm_fact fixCons conservation where
  base := fixRca0
  scope := provability
  formulaClass := fixPi11
  lhs := [smokeVariant]
  rhs := [smokePropVariant]
  note := "fixture conservation record"

-- Fail-closed rendering, pinned: every fact is recorded, none is supported.
/--
info: facts (4):
  fixCons [conservation | theory fixRca0 provability] smokeVariant conservative[fixPi11] over smokePropVariant — recorded, no evidence linked
    note: fixture conservation record
  fixImp [implication | theory fixRca0 provability] smokePropVariant+smokeVariant => smokePropVariant — recorded, no evidence linked
  fixImpOmega [implication | theory fixRca0 omegaModels] smokePropVariant+smokeVariant => smokePropVariant — recorded, no evidence linked
  fixRed [reducibility | uniform fixWeihrauch] smokeProblemA <= smokeProblemB [representative] — recorded, no evidence linked
base theories (2): fixRca0, rca0
formula classes (1): fixPi11
reducibility notions (1): fixWeihrauch
semantic contexts (1): rca0.turingIdealOmega
-/
#guard_msgs in
#rm_facts

/-! ### Typed semantic certificates and the scoped reporting split (#6)

A kernel-checked `semanticImplication` record must cite a
`SemanticImplicationCertificate Base P Q` validated against a **registered semantic
context**: exact base predicate, matching (never escalated) scope, and endpoints at the
context's model-indexed layer — an ambient variant is never substituted. The resulting claim
renders and counts as a *certified ω-model implication*, never an unqualified RM bound. -/

/-- A fixture model type for semantic-certificate tests. -/
structure SmokeModel where
  /-- A stand-in second-order part. -/
  sets : Nat → Prop

/-- The fixture model layer's interface schema. -/
abbrev SmokeModelInterface := SmokeModel → Prop

rm_semantic_layer smokemodellayer "fixture model layer"
  interfaceSchema := SmokeModelInterface

/-- The fixture base context (an RCAω stand-in). -/
def SmokeBaseCtx : SmokeModel → Prop := fun _ => True

/-- A model-indexed fixture principle. -/
def SmokeModelP : SmokeModel → Prop := fun M => M.sets 0

/-- A model-indexed fixture target. -/
def SmokeModelQ : SmokeModel → Prop := fun M => M.sets 0 ∨ M.sets 1

rm_semantic_context smokeCtx where
  base := fixRca0
  scope := omegaModels
  layer := smokemodellayer
  decl := RMSmoke.SmokeBaseCtx
  description := "fixture ω-model context"

-- provability is not a model class.
/--
error: concept catalog: a semantic context's scope must be omegaModels or allModels — provability is not a model class
-/
#guard_msgs in
rm_semantic_context smokeBadCtx where
  base := fixRca0
  scope := provability
  layer := smokemodellayer
  decl := RMSmoke.SmokeBaseCtx
  description := "rejected"

-- The context predicate must live at the layer's model type.
/--
error: concept catalog: context predicate 'RMSmoke.smokeProp' must have type 'RMSmoke.SmokeModelInterface' (the interface schema of layer 'smokemodellayer') up to definitional equality
-/
#guard_msgs in
rm_semantic_context smokeBadCtx2 where
  base := fixRca0
  scope := omegaModels
  layer := smokemodellayer
  decl := RMSmoke.smokeProp
  description := "rejected"

rm_statement_variant smokeModelVarP where
  concept := smokeConcept
  layer := smokemodellayer
  interface := RMSmoke.SmokeModelP
  description := "fixture model-indexed principle"

rm_statement_variant smokeModelVarQ where
  concept := smokeConcept
  layer := smokemodellayer
  interface := RMSmoke.SmokeModelQ
  description := "fixture model-indexed target"

/-- The typed ω certificate: the implication over every model of the exact base context. -/
theorem smokeSemCert :
    ReverseMathlib.Meta.SemanticImplicationCertificate SmokeBaseCtx SmokeModelP SmokeModelQ :=
  ⟨fun _ _ h => Or.inl h⟩

-- Kernel-checked semantic evidence without a registered context is rejected.
/--
error: registry: kernel-checked semanticImplication evidence must name its registered semantic context (context ...); a free-floating model quantification certifies nothing
-/
#guard_msgs in
revmath_port noCtxPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    via RMSmoke.smokeSemCert
    assumes smokeModelVarP

-- The evidence scope must match the registered context's scope; never escalated.
/--
error: registry: evidence scope 'ReverseMathlib.Meta.SemanticScope.allModels' does not match the registered scope of semantic context 'smokeCtx' ('omegaModels'); scopes are never escalated or defaulted
-/
#guard_msgs in
revmath_port escalatedPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope allModels
    context smokeCtx
    via RMSmoke.smokeSemCert
    assumes smokeModelVarP

-- An ambient variant is never substituted for a model-indexed one.
/--
error: registry: assumed variant 'smokeVariant' is at layer 'ambient', not the semantic context's layer 'smokemodellayer'; an ambient variant is never substituted for a model-indexed one
-/
#guard_msgs in
revmath_port ambientSubPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    context smokeCtx
    via RMSmoke.smokeSemCert
    assumes smokeVariant

-- The literal True.intro is not a semantic certificate.
/--
error: registry: 'True.intro' does not have type 'ReverseMathlib.Meta.SemanticImplicationCertificate _ _ _' (found 'True'); a kernel-checked semanticImplication citation must be a typed semantic certificate
-/
#guard_msgs in
revmath_port bogusSemPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    context smokeCtx
    via True.intro
    assumes smokeModelVarP

-- Direction-aware: an upper-shaped semantic certificate is rejected as lower evidence.
/--
error: registry: semantic certificate 'RMSmoke.smokeSemCert' assumes 'SmokeModelP', which is not definitionally the required source interface 'RMSmoke.SmokeModelQ'
-/
#guard_msgs in
revmath_port wrongDirSemPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication lower kernelChecked modelSemantics scope omegaModels
    context smokeCtx
    via RMSmoke.smokeSemCert
    assumes smokeModelVarP

-- ACCEPT: the first certified ω-scope claim in the fixture registry.
revmath_port omegaFixture where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    context smokeCtx
    via RMSmoke.smokeSemCert
    assumes smokeModelVarP

-- Renders as a certified ω-model implication — never an unqualified "RM bound".
/--
info: omegaFixture
  mathlib: RMSmoke.smokeProp
  target: reverse-mathlib:smokeModelVarQ
  port: RMSmoke.SmokeModelQ
  source relation: conceptual analogue
  upper · semantic implication: kernel checked
    certificate: RMSmoke.smokeSemCert (assumes smokeModelVarP)
    ambient: model semantics; RM semantic scope: all ω-models
    semantic context: smokeCtx
  candidate classical classification: unknown
  certified ω-model implication (all ω-models, upper)
  exact lower bound: pending
-/
#guard_msgs in
#revmath_port? omegaFixture

-- route/artifact belong to syntacticDerivation only …
/-- error: registry: only syntacticDerivation evidence may carry a proof route -/
#guard_msgs in
revmath_port strayRoutePort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof lower claimed lean route direct
    assumes smokeVariant

-- … and register as provenance/artifact data on claimed syntactic evidence.
revmath_port routedPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence syntacticDerivation upper claimed objectTheory theory smokeTheory
    route semanticCompleteness artifact propositionOnly

-- The per-scope scoreboard: exactly one certified ω-model implication, nothing escalated.
/--
info: concepts: 4; variants: 9; ports: 5; evidence: 7 (5 kernel checked, 2 claimed, 0 backend checked); certified unique facts — ω-model: 0; all-model: 0; syntactic: 0
-/
#guard_msgs in
#revmath_stats

-- The ambient-factorization graph is untouched by semantic evidence: still no edge into or
-- out of the model-indexed interfaces.
#eval show CoreM Unit from do
  let env ← getEnv
  let snap := CatalogSnapshot.ofEnv env
  check (!snap.ambientEdges.any fun e =>
      e.source == `RMSmoke.SmokeModelP || e.target == `RMSmoke.SmokeModelQ ||
        e.source == `RMSmoke.SmokeModelQ || e.target == `RMSmoke.SmokeModelP)
    "semantic evidence must not add ambient-factorization edges"

/-! ### Fact certification (#24)

The semantic certificate is evidence for the **fact**; base, scope, direction, and
endpoints derive from the fact, never repeated freely. Only singleton
implication/equivalence facts certify; everything else is fail-closed. The headline counts
unique certified facts, so neither multiple certificates nor port evidence inflate it. -/

rm_fact fixOmegaFact implication where
  base := fixRca0
  scope := omegaModels
  lhs := [smokeModelVarP]
  rhs := [smokeModelVarQ]

rm_fact fixOmegaConj implication where
  base := fixRca0
  scope := omegaModels
  lhs := [smokeModelVarP, smokeModelVarQ]
  rhs := [smokeModelVarQ]

-- Unknown fact and unknown context are rejected.
/-- error: registry: unknown fact 'noSuchFact' -/
#guard_msgs in
revmath_certify_fact noSuchFact where
  context := smokeCtx
  via := RMSmoke.smokeSemCert

/-- error: registry: unknown semantic context 'noSuchCtx' -/
#guard_msgs in
revmath_certify_fact fixOmegaFact where
  context := noSuchCtx
  via := RMSmoke.smokeSemCert

-- The fact's scope must be the context's scope — a provability fact cannot borrow an
-- ω context.
/--
error: registry: fact 'fixImp' has scope 'provability', which is not the semantic context's scope 'omegaModels'; scopes are never escalated or defaulted
-/
#guard_msgs in
revmath_certify_fact fixImp where
  context := smokeCtx
  via := RMSmoke.smokeSemCert

-- Uniform facts have no schema.
/--
error: registry: uniform facts have no semantic-certificate schema; only theory-context facts can be certified
-/
#guard_msgs in
revmath_certify_fact fixRed where
  context := smokeCtx
  via := RMSmoke.smokeSemCert

-- Endpoints must live at the context's layer — a singleton fact over ambient variants is
-- rejected even at the right scope.
rm_fact fixAmbientOmega implication where
  base := fixRca0
  scope := omegaModels
  lhs := [smokeVariant]
  rhs := [smokePropVariant]

/--
error: registry: endpoint variant 'smokeVariant' is at layer 'ambient', not the semantic context's layer 'smokemodellayer'; an ambient variant is never substituted for a model-indexed one
-/
#guard_msgs in
revmath_certify_fact fixAmbientOmega where
  context := smokeCtx
  via := RMSmoke.smokeSemCert

-- Conjunction certificates are rejected fail-closed.
/--
error: registry: conjunction certificates are rejected fail-closed until conjunction semantics exists (the lhs of 'fixOmegaConj' has 2 conjuncts)
-/
#guard_msgs in
revmath_certify_fact fixOmegaConj where
  context := smokeCtx
  via := RMSmoke.smokeSemCert

-- The literal True.intro is not a certificate for a fact either.
/--
error: registry: 'True.intro' does not have type 'ReverseMathlib.Meta.SemanticImplicationCertificate _ _ _' (found 'True'); a kernel-checked semanticImplication citation must be a typed semantic certificate
-/
#guard_msgs in
revmath_certify_fact fixOmegaFact where
  context := smokeCtx
  via := True.intro

-- ACCEPT: the first certified fact.
revmath_certify_fact fixOmegaFact where
  context := smokeCtx
  via := RMSmoke.smokeSemCert
  note := "fixture certification"

-- Duplicate certification via the same certificate is rejected.
/-- error: registry: fact 'fixOmegaFact' is already certified via 'RMSmoke.smokeSemCert' -/
#guard_msgs in
revmath_certify_fact fixOmegaFact where
  context := smokeCtx
  via := RMSmoke.smokeSemCert

-- Ports may cross-link the fact, on semanticImplication evidence only.
/-- error: registry: only semanticImplication evidence may cross-link a fact -/
#guard_msgs in
revmath_port strayFactLinkPort where
  mathlib := RMSmoke.smokeProp
  target := smokePropVariant
  relation := conceptualAnalogue
  evidence relativeProof lower claimed lean
    assumes smokeVariant
    fact fixOmegaFact

revmath_port linkedOmegaPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarQ
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    context smokeCtx
    via RMSmoke.smokeSemCert
    assumes smokeModelVarP
    fact fixOmegaFact

/-! #### The equivalence path (production will certify an equivalence, so it is pinned) -/

/-- A defeq-distinct but equivalent model predicate, for the equivalence-certificate path. -/
def SmokeModelP' : SmokeModel → Prop := fun M => M.sets 0 ∧ True

rm_statement_variant smokeModelVarPAlt where
  concept := smokeConcept
  layer := smokemodellayer
  interface := RMSmoke.SmokeModelP'
  description := "fixture model-indexed principle, equivalent alternative form"

rm_fact fixEqFact equivalence where
  base := fixRca0
  scope := omegaModels
  lhs := [smokeModelVarP]
  rhs := [smokeModelVarPAlt]

/-- The exact equivalence certificate, sides in the fact's order. -/
theorem smokeSemEqCert : ReverseMathlib.Meta.SemanticEquivalenceCertificate
    SmokeBaseCtx SmokeModelP SmokeModelP' :=
  ⟨fun _ _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩⟩

/-- The same equivalence with flipped sides — must also be accepted. -/
theorem smokeSemEqCertFlipped : ReverseMathlib.Meta.SemanticEquivalenceCertificate
    SmokeBaseCtx SmokeModelP' SmokeModelP :=
  ⟨fun _ _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩

/-- An implication-shaped certificate with the right endpoints — still rejected for an
equivalence fact. -/
theorem smokeSemCertPAlt : ReverseMathlib.Meta.SemanticImplicationCertificate
    SmokeBaseCtx SmokeModelP SmokeModelP' :=
  ⟨fun _ _ h => ⟨h, trivial⟩⟩

/--
error: registry: 'RMSmoke.smokeSemCertPAlt' does not have type 'ReverseMathlib.Meta.SemanticEquivalenceCertificate _ _ _' (found 'SemanticImplicationCertificate
  SmokeBaseCtx SmokeModelP
  SmokeModelP''); a kernel-checked semanticImplication citation must be a typed semantic certificate
-/
#guard_msgs in
revmath_certify_fact fixEqFact where
  context := smokeCtx
  via := RMSmoke.smokeSemCertPAlt

-- ACCEPT: exact certificate, then the flipped-side certificate on the same fact.
revmath_certify_fact fixEqFact where
  context := smokeCtx
  via := RMSmoke.smokeSemEqCert

revmath_certify_fact fixEqFact where
  context := smokeCtx
  via := RMSmoke.smokeSemEqCertFlipped

-- A port cross-link whose endpoints do not match the fact is rejected — display metadata
-- must not be able to lie.
/--
error: registry: evidence direction/endpoints do not match cross-linked fact 'fixOmegaFact' (an implication link must respect orientation; an equivalence link must be exact-direction over the fact's endpoint pair)
-/
#guard_msgs in
revmath_port mismatchedLinkPort where
  mathlib := RMSmoke.smokeProp
  target := smokeModelVarP
  relation := conceptualAnalogue
  evidence semanticImplication upper kernelChecked modelSemantics scope omegaModels
    context smokeCtx
    via RMSmoke.smokeSemCert
    assumes smokeModelVarQ
    fact fixOmegaFact

-- The evidence-aware fact view: certified facts render certificates and the
-- context-realization status; everything else stays recorded-but-unsupported.
/--
info: facts (8):
  fixAmbientOmega [implication | theory fixRca0 omegaModels] smokeVariant => smokePropVariant — recorded, no evidence linked
  fixCons [conservation | theory fixRca0 provability] smokeVariant conservative[fixPi11] over smokePropVariant — recorded, no evidence linked
  fixEqFact [equivalence | theory fixRca0 omegaModels] smokeModelVarP <=> smokeModelVarPAlt — CERTIFIED
    via RMSmoke.smokeSemEqCert [context smokeCtx]
      realization: equivalence kernel-checked over 'RMSmoke.SmokeBaseCtx'; context status: fixture ω-model context
    via RMSmoke.smokeSemEqCertFlipped [context smokeCtx]
      realization: equivalence kernel-checked over 'RMSmoke.SmokeBaseCtx'; context status: fixture ω-model context
  fixImp [implication | theory fixRca0 provability] smokePropVariant+smokeVariant => smokePropVariant — recorded, no evidence linked
  fixImpOmega [implication | theory fixRca0 omegaModels] smokePropVariant+smokeVariant => smokePropVariant — recorded, no evidence linked
  fixOmegaConj [implication | theory fixRca0 omegaModels] smokeModelVarP+smokeModelVarQ => smokeModelVarQ — recorded, no evidence linked
  fixOmegaFact [implication | theory fixRca0 omegaModels] smokeModelVarP => smokeModelVarQ — CERTIFIED
    via RMSmoke.smokeSemCert [context smokeCtx]
      note: fixture certification
      realization: implication kernel-checked over 'RMSmoke.SmokeBaseCtx'; context status: fixture ω-model context
  fixRed [reducibility | uniform fixWeihrauch] smokeProblemA <= smokeProblemB [representative] — recorded, no evidence linked
-/
#guard_msgs in
#revmath_facts

-- The headline counts UNIQUE certified facts: one ω-model fact, despite two ports carrying
-- semantic evidence for the same content.
/--
info: concepts: 4; variants: 10; ports: 6; evidence: 8 (6 kernel checked, 2 claimed, 0 backend checked); certified unique facts — ω-model: 2; all-model: 0; syntactic: 0
-/
#guard_msgs in
#revmath_stats

end RMSmoke
