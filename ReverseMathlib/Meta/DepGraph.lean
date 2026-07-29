/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean

/-!
# Dependency graph mining

The core library behind `#rm_deps`, `#rm_frontier`, and the `#rm_assert_*` commands
(`ReverseMathlib.Meta.Commands`). It extracts the exact constant-dependency graph of a
declaration by walking types and bodies itself, and computes three closures:

* **statement closure**: BFS seeded from the constants of the target's *type*. At every reached
  declaration both its type and its available value are followed, because a declaration's type is
  required to check any use of it.
* **value closure**: the same BFS seeded from the constants of the target's *value* (for
  inductives and recursors, from their declaration-group members).
* **proof-only closure**: `valueClosure \ statementClosure` — the constants a proof uses beyond
  what its statement already requires. This is the load-bearing report: two proofs of the same
  statement can have radically different proof-only closures while sharing identical kernel
  axioms, which is exactly the difference between axiom auditing and strength auditing.

Design notes:

* We cannot reuse `Lean.collectAxioms` for the graph: on this toolchain it reads axiom sets
  precomputed at olean-export time for imported declarations and never walks their bodies. We
  mirror its traversal architecture (kernel-environment lookup with exporting disabled, so
  `private` bodies are visible) but retain all edges.
* Edges carry a kind bitset: `typeDep`, `valueDep`, and `declarationGroupDep`. Group edges are
  synthesized only for inductive → constructors and recursor → associated inductives.
  Constructor → inductive is *not* synthesized: it already appears naturally as a `typeDep`,
  since a constructor's result type mentions its inductive.
* `Quot` primitives are classified as terminal kernel primitives, not "unknown"; `unknown` is
  reserved for constants genuinely absent from the kernel environment, so unknowns stay
  fail-closed.
* Traversal is bounded by `maxNodes`; a truncated result is marked and must be treated as
  incomplete by all consumers (assertions *fail* on truncated graphs).
* Instance-synthesis provenance is not recoverable from elaborated terms; nodes carry an
  `isInstance` flag instead, and reports may count instances but never claim synthesis edges.

`#rm_slice` (mechanical lambda-abstraction of frontier constants out of a proof term) is
deliberately **not** implemented. Known hard parts recorded for a future attempt: the same
universe-polymorphic constant may occur at several instantiations; constants may occur
dependently inside types; inter-dependent frontier constants must be abstracted in topological
order. Hand-written relative theorems are the slicing mechanism until several real proof terms
have been studied.
-/

namespace ReverseMathlib.Meta

open Lean

/-- Kinds of dependency edge, as a bitset. A single edge may be several kinds at once (e.g. a
constant used in both the type and the value of the source). -/
structure DepKinds where
  /-- The target occurs in the source's type. -/
  typeDep : Bool := false
  /-- The target occurs in the source's value (proof term or definition body). -/
  valueDep : Bool := false
  /-- Structural declaration-group edge: inductive → constructor, or recursor → associated
  inductive. Not an occurrence in a type or value. -/
  declarationGroupDep : Bool := false
  deriving Inhabited, Repr, BEq

namespace DepKinds

/-- Bitset union of two edge-kind sets. -/
def merge (a b : DepKinds) : DepKinds where
  typeDep := a.typeDep || b.typeDep
  valueDep := a.valueDep || b.valueDep
  declarationGroupDep := a.declarationGroupDep || b.declarationGroupDep

/-- A pure type-occurrence edge. -/
def type : DepKinds := { typeDep := true }

/-- A pure value-occurrence edge. -/
def value : DepKinds := { valueDep := true }

/-- A pure declaration-group edge. -/
def group : DepKinds := { declarationGroupDep := true }

end DepKinds

/-- Classification of a graph node. `quotPrimitive` marks the understood terminal kernel
primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`); `unknown` is reserved for constants
absent from the kernel environment, so that "unknown" remains a genuinely fail-closed category. -/
inductive NodeClass where
  /-- An `axiom` declaration. -/
  | axiomDecl
  /-- A `def`. -/
  | defnDecl
  /-- A `theorem`. -/
  | thmDecl
  /-- An `opaque` declaration (its value, when recorded, is still traversed). -/
  | opaqueDecl
  /-- An inductive type. -/
  | inductiveDecl
  /-- A constructor. -/
  | ctorDecl
  /-- A recursor. -/
  | recDecl
  /-- A `Quot` kernel primitive: understood and terminal, not unknown. -/
  | quotPrimitive
  /-- Not found in the kernel environment. -/
  | unknown
  deriving Inhabited, Repr, BEq

/-- Metadata recorded for each node of the dependency graph. -/
structure NodeInfo where
  /-- Classification of the constant. -/
  cls : NodeClass
  /-- Owning module, if the constant is imported; `none` for current-file constants. -/
  module? : Option Name := none
  /-- Whether the constant is registered as a typeclass instance. Provenance only: reports may
  count instances, but instance-synthesis edges are not recoverable and never claimed. -/
  isInstance : Bool := false
  deriving Inhabited, Repr

/-- A dependency graph: node metadata plus adjacency with kind-bitset edges. -/
structure DepGraph where
  /-- Node metadata, keyed by constant name. -/
  nodes : Std.HashMap Name NodeInfo := {}
  /-- Adjacency: for each expanded source, its direct dependencies with edge kinds. -/
  edges : Std.HashMap Name (Std.HashMap Name DepKinds) := {}
  deriving Inhabited

/-- Configuration for a mining run. -/
structure MineConfig where
  /-- Maximum number of constants visited per closure computation. Exceeding it marks the result
  truncated; consumers must treat truncated results as incomplete. -/
  maxNodes : Nat := 500000
  /-- Frontier constants: recorded as cut points when reached, but never expanded. Empty for the
  raw closure, which is invariant under frontier registration by construction. -/
  stopAt : NameSet := {}

/-- Mutable state threaded through mining runs, so several closures over the same environment
share node and edge computations. -/
structure MineState where
  /-- The accumulated graph. -/
  graph : DepGraph := {}
  /-- Frontier constants actually reached (and therefore cut) during mining. -/
  cuts : NameSet := {}
  deriving Inhabited

/-- Classify a constant. -/
def classify : ConstantInfo → NodeClass
  | .axiomInfo _ => .axiomDecl
  | .defnInfo _ => .defnDecl
  | .thmInfo _ => .thmDecl
  | .opaqueInfo _ => .opaqueDecl
  | .inductInfo _ => .inductiveDecl
  | .ctorInfo _ => .ctorDecl
  | .recInfo _ => .recDecl
  | .quotInfo _ => .quotPrimitive

/-- Direct dependency edges of a constant, with kind bitsets, deduplicated.

Type constants are `typeDep`; value constants (via `ConstantInfo.value? (allowOpaque := true)`,
so recorded opaque bodies are traversed rather than treated as unknown) are `valueDep`;
inductive → constructors and recursor → associated inductives are `declarationGroupDep`.
`Quot` primitives get no outgoing edges (terminal). -/
def directDeps (ci : ConstantInfo) : Std.HashMap Name DepKinds := Id.run do
  let mut acc : Std.HashMap Name DepKinds := {}
  let add (m : Std.HashMap Name DepKinds) (n : Name) (k : DepKinds) : Std.HashMap Name DepKinds :=
    m.insert n ((m.getD n {}).merge k)
  if let .quotInfo _ := ci then
    return acc
  for c in ci.type.getUsedConstants do
    acc := add acc c .type
  if let some v := ci.value? (allowOpaque := true) then
    for c in v.getUsedConstants do
      acc := add acc c .value
  match ci with
  | .inductInfo v => for c in v.ctors do acc := add acc c .group
  | .recInfo v => for c in v.all do acc := add acc c .group
  | _ => pure ()
  return acc

/-- Seeds for the two closures of a target: constants of its type (statement seeds) and
constants of its value together with its declaration-group members (value seeds). -/
def seedsOf (ci : ConstantInfo) : Array Name × Array Name := Id.run do
  let stmtSeeds := ci.type.getUsedConstants
  let mut valSeeds : Array Name := #[]
  if let some v := ci.value? (allowOpaque := true) then
    valSeeds := v.getUsedConstants
  match ci with
  | .inductInfo v => valSeeds := valSeeds ++ v.ctors.toArray
  | .recInfo v => valSeeds := valSeeds ++ v.all.toArray
  | _ => pure ()
  return (stmtSeeds, valSeeds)

/-- Look up a constant the way `Lean.collectAxioms` does: in the kernel environment with
exporting disabled, so `private` bodies are visible and results match what the kernel checked. -/
def kernelFind (env : Environment) (c : Name) : Option ConstantInfo :=
  (env.setExporting false).checked.get.find? c

/-- Node metadata for a constant in `env` (the elaboration environment, used for module and
instance lookup). -/
def nodeInfoFor (env : Environment) (c : Name) (ci? : Option ConstantInfo) : NodeInfo :=
  let module? := do
    let idx ← env.getModuleIdxFor? c
    (env.allImportedModuleNames)[idx.toNat]?
  { cls := ci?.map classify |>.getD .unknown
    module? := module?
    isInstance := Meta.isInstanceCore env c }

/-- Ensure `c` has node metadata and (unless terminal) edges recorded in the graph; return the
updated graph and `c`'s direct dependency names. Cached: an already-expanded constant is not
recomputed. -/
def expand (env : Environment) (st : DepGraph) (c : Name) : DepGraph × Array Name := Id.run do
  if let some tgts := st.edges[c]? then
    return (st, tgts.keysArray)
  let ci? := kernelFind env c
  let info := nodeInfoFor env c ci?
  let deps : Std.HashMap Name DepKinds := match ci? with
    | some ci => directDeps ci
    | none => {}
  let st := { st with nodes := st.nodes.insert c info, edges := st.edges.insert c deps }
  return (st, deps.keysArray)

/-- Result of one BFS closure computation. -/
structure ClosureResult where
  /-- The constants reached (not including unexpanded frontier cut points' dependencies). -/
  reached : NameSet := {}
  /-- Whether the traversal hit `maxNodes` and stopped early. A truncated closure is incomplete
  and must fail any hard assertion. -/
  truncated : Bool := false
  deriving Inhabited

/-- BFS from `seeds` over the dependency graph, expanding every reached constant except
registered frontier cut points, which are recorded in `MineState.cuts` but not expanded.
Bounded by `cfg.maxNodes`. -/
def mineFrom (env : Environment) (cfg : MineConfig) (st : MineState) (seeds : Array Name) :
    MineState × ClosureResult := Id.run do
  let mut graph := st.graph
  let mut cuts := st.cuts
  let mut reached : NameSet := {}
  let mut count : Nat := 0
  let mut truncated := false
  let mut queue := seeds
  let mut qi : Nat := 0
  while h : qi < queue.size do
    let c := queue[qi]
    qi := qi + 1
    if reached.contains c then
      continue
    if count ≥ cfg.maxNodes then
      truncated := true
      break
    reached := reached.insert c
    count := count + 1
    let (graph', deps) := expand env graph c
    graph := graph'
    if cfg.stopAt.contains c then
      cuts := cuts.insert c
    else
      for d in deps do
        unless reached.contains d do
          queue := queue.push d
  return ({ graph, cuts }, { reached, truncated })

/-- Full mining result for a single target declaration. -/
structure MineResult where
  /-- The declaration that was mined. -/
  target : Name
  /-- Graph and cut set accumulated over both closure runs. -/
  state : MineState
  /-- Direct dependencies of the target itself, with edge kinds. -/
  direct : Std.HashMap Name DepKinds
  /-- Closure seeded from the target's type. -/
  statement : ClosureResult
  /-- Closure seeded from the target's value / declaration group. -/
  value : ClosureResult
  deriving Inhabited

namespace MineResult

/-- Whether either closure is incomplete. Hard assertions must fail when this holds. -/
def truncated (r : MineResult) : Bool :=
  r.statement.truncated || r.value.truncated

/-- Union of the statement and value closures. -/
def totalClosure (r : MineResult) : NameSet :=
  r.statement.reached.foldl (init := r.value.reached) fun s n => s.insert n

/-- `valueClosure \ statementClosure`: what the proof uses beyond its statement. -/
def proofOnlyClosure (r : MineResult) : NameSet :=
  r.value.reached.foldl (init := {}) fun s n =>
    if r.statement.reached.contains n then s else s.insert n

/-- Names in the total closure whose node has the given class, sorted. -/
def nodesOfClass (r : MineResult) (cls : NodeClass) : Array Name :=
  let names := r.totalClosure.foldl (init := #[]) fun a n =>
    if (r.state.graph.nodes[n]?).any (·.cls == cls) then a.push n else a
  names.qsort Name.lt

/-- Kernel axioms reached (in either closure), sorted. -/
def axioms (r : MineResult) : Array Name := r.nodesOfClass .axiomDecl

/-- Constants absent from the kernel environment, sorted. Fail-closed: this is only for
genuinely unresolvable constants, never for understood primitives. -/
def unknowns (r : MineResult) : Array Name := r.nodesOfClass .unknown

end MineResult

/-- Mine a single target declaration: record its own node and direct edges, then compute the
statement closure and the value closure (sharing one graph cache). -/
def mineTarget (env : Environment) (cfg : MineConfig) (target : Name) :
    Except String MineResult := do
  let some ci := kernelFind env target
    | throw s!"unknown constant '{target}'"
  let (stmtSeeds, valSeeds) := seedsOf ci
  let direct := directDeps ci
  let nodes0 : Std.HashMap Name NodeInfo := {}
  let nodes0 := nodes0.insert target (nodeInfoFor env target (some ci))
  let st : MineState := { graph := { nodes := nodes0 } }
  let (st, statement) := mineFrom env cfg st stmtSeeds
  let (st, value) := mineFrom env cfg st valSeeds
  return { target, state := st, direct, statement, value }

end ReverseMathlib.Meta
