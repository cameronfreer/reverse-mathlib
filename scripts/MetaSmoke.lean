/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Basic
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

def smokeProp : Prop := True
def otherProp : Prop := (2 : ℕ) = 2

/-- A kernel-checked theorem of certificate *shape* but the wrong *type*: its assumption is not
the registered interface of the principle it will claim to assume. -/
theorem bogusCert : ReverseMathlib.Meta.RelativeCertificate ((1 : ℕ) = 1) smokeProp :=
  ⟨fun _ => trivial⟩

rm_principle smokeTestPrinciple where
  description := "test principle"
  interface := RMSmoke.otherProp

/-- error: registry: duplicate principle id 'smokeTestPrinciple' -/
#guard_msgs in
rm_principle smokeTestPrinciple where
  description := "duplicate"
  interface := RMSmoke.otherProp

/--
error: registry: certificate 'RMSmoke.bogusCert' assumes '1 =
  1', which is not definitionally the registered interface 'RMSmoke.otherProp' of the cited principle
-/
#guard_msgs in
revmath_port bogusPort where
  mathlib := RMSmoke.smokeProp
  port := RMSmoke.smokeProp
  relation := conceptualAnalogue
  evidence relativeProof upper kernelChecked lean
    via RMSmoke.bogusCert
    assumes smokeTestPrinciple

/--
error: registry: ambient-Lean evidence carries no RM semantic scope; remove the scope or change the ambient
-/
#guard_msgs in
revmath_port scopedPort where
  mathlib := RMSmoke.smokeProp
  port := RMSmoke.smokeProp
  relation := conceptualAnalogue
  evidence relativeProof upper claimed lean scope omegaModels

/-- error: registry: duplicate port id 'countableHall' -/
#guard_msgs in
revmath_port countableHall where
  mathlib := RMSmoke.smokeProp
  port := RMSmoke.smokeProp
  relation := conceptualAnalogue

-- The walking slice's honest verdict, pinned.
/--
info: countableHall
  mathlib: Finset.all_card_le_biUnion_card_iff_exists_injective
  port: ReverseMathlib.Standard.CountableHall
  source relation: proof analogue / mined architecture
  upper · relative Lean factorization: kernel checked
    certificate: ReverseMathlib.Ports.countableHallRelativeCertificate (assumes explicitFiniteInverseLimitCompactness)
    ambient: unrestricted Lean over standard ℕ; RM semantic scope: none
    note: Proof-only closure certified by CI (scripts/MetaSmoke.lean): contains finite Hall, excludes the infinite Hall theorem, the compactness boundary, and the selection scaffolding.
  candidate classical classification: WKL₀ for this explicitly-Finset presentation (cf. Hirst, marriage theorems; presentation-sensitive) [claimed, UNVERIFIED]
  backend RM certificate: pending
  exact lower bound: pending
  note: Mined from mathlib's proof: finite Hall reused for level nonemptiness; the topological compactness boundary (nonempty_sections_of_finite_inverse_system, ultimately Tychonoff) and the hallMatchingsOn selection scaffolding replaced by the EFILC hypothesis over explicitly enumerated Finset fibers — no Nonempty-instance extraction step remains (occurrence-level fact; see scripts/MetaSmoke.lean for the constant-level gates and the recorded indefiniteDescription granularity limitation).
-/
#guard_msgs in
#revmath_port? countableHall

/--
info: principles: 2; ports: 1; evidence: 1 (1 kernel checked, 0 claimed, 0 backend checked); certified RM bounds: 0
-/
#guard_msgs in
#revmath_stats

end RMSmoke
