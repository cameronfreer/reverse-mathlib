/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean

/-!
# Conceptual identities and typed external references

The conceptual catalog (issue #3), **additive**: today's `PrincipleId` registry remains the
capability layer until issue #4 migrates it; nothing here owns a Lean proposition.

Layered identity, enforced by distinct newtypes so concept/variant/problem confusion is a
compile-time error:

* `ConceptId` — a conceptual family (`reverse-mathlib:wkl`); **no privileged Lean
  proposition**;
* `StatementVariantId` — an exact statement variant
  (`reverse-mathlib:wkl.binaryTree.omegaModel`); may own a Lean interface (from #4);
* `UniformProblemId` — a represented computational problem
  (`reverse-mathlib:wkl.binaryPathChoice.cantorRepresentation`, from #4).

External references are typed: a namespace (registered, never a hard-coded allowlist), a
string key (Simpson references, DOIs, workbook rows, and RMZoo symbols are not Lean names), a
tagged target, and a relation. **Only `exactAlias` participates in identity resolution**;
`sourceLocation`, `importedCorrespondence`, and `relatedVariant` are provenance and may
legitimately appear on several targets. Exact aliases are a direct map
`(namespace, key) ↦ target` — no alias chains, so resolution is trivial and acyclic.

## Import-wide collision handling

Registration-time checks in one module are **not sufficient**: two sibling modules can
independently register the same concept or the same exact alias and only collide when a third
module imports both — the persistent extensions simply concatenate imported arrays. So the
authoritative state is `ConceptCatalog.ofEnv`, which folds every entry (imported and local)
into an indexed catalog **plus accumulated conflicts**, and every query/export command goes
through `requireCleanCatalog`, which rejects a conflicted state outright. Registration
commands additionally run the same fold for early, well-located errors.
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- A conceptual family identifier. Carries **no** Lean proposition. -/
structure ConceptId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- An exact statement-variant identifier (populated by issue #4). -/
structure StatementVariantId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- A represented uniform-problem identifier (populated by issue #4). -/
structure UniformProblemId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

instance : ToString ConceptId := ⟨fun c => toString c.name⟩
instance : ToString StatementVariantId := ⟨fun v => toString v.name⟩
instance : ToString UniformProblemId := ⟨fun q => toString q.name⟩

/-- A typed reference to a catalog object. -/
inductive CatalogObjectRef where
  /-- A conceptual family. -/
  | concept (id : ConceptId)
  /-- An exact statement variant. -/
  | statement (id : StatementVariantId)
  /-- A represented uniform problem. -/
  | uniformProblem (id : UniformProblemId)
  deriving Inhabited, Repr, BEq

/-- Stable serialization of a catalog object reference: kind tag plus prefixed id. -/
def CatalogObjectRef.kindTag : CatalogObjectRef → String
  | .concept _ => "concept"
  | .statement _ => "statement"
  | .uniformProblem _ => "uniformProblem"

/-- The underlying name of a reference. -/
def CatalogObjectRef.name : CatalogObjectRef → Name
  | .concept i => i.name
  | .statement i => i.name
  | .uniformProblem i => i.name

/-- An external namespace identifier (`rmzoo`, `simpson`, `concordance`, `sanders`, …) —
registered through `rm_namespace`, never a hard-coded allowlist. -/
structure ExternalNamespaceId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- How an external key relates to its target. Only `exactAlias` participates in identity
resolution. -/
inductive ExternalRefRelation where
  /-- The external key denotes exactly this catalog object. Resolvable. -/
  | exactAlias
  /-- A source/theorem location (e.g. `simpson:I.10`). Provenance only. -/
  | sourceLocation
  /-- An imported record corresponding to this object (e.g. `concordance:C085`). Provenance
  only. -/
  | importedCorrespondence
  /-- A related but distinct variant. Provenance only. -/
  | relatedVariant
  deriving Inhabited, Repr, BEq

/-- Stable tag for an external-reference relation. -/
def ExternalRefRelation.tag : ExternalRefRelation → String
  | .exactAlias => "exactAlias"
  | .sourceLocation => "sourceLocation"
  | .importedCorrespondence => "importedCorrespondence"
  | .relatedVariant => "relatedVariant"

/-- A typed external reference. Keys are strings — Simpson references, DOIs, workbook rows,
and RMZoo symbols are not Lean names. -/
structure ExternalRef where
  /-- The registered namespace. -/
  ns : ExternalNamespaceId
  /-- The external key. -/
  key : String
  /-- The typed target. -/
  target : CatalogObjectRef
  /-- The relation of key to target. -/
  relation : ExternalRefRelation
  deriving Inhabited, Repr, BEq

/-- A registered conceptual family. Deliberately has no Lean-proposition field. -/
structure ConceptEntry where
  /-- The open identifier. -/
  id : ConceptId
  /-- Informal description. -/
  description : String
  /-- Display label — presentation metadata, separate from mathematics. -/
  displayLabel : String
  deriving Inhabited, Repr, BEq

/-- A registered external namespace. -/
structure ExternalNamespaceEntry where
  /-- The namespace identifier. -/
  id : ExternalNamespaceId
  /-- What the namespace's keys denote. -/
  description : String
  deriving Inhabited, Repr, BEq

initialize conceptExt : SimplePersistentEnvExtension ConceptEntry (Array ConceptEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize namespaceExt :
    SimplePersistentEnvExtension ExternalNamespaceEntry (Array ExternalNamespaceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize externalRefExt : SimplePersistentEnvExtension ExternalRef (Array ExternalRef) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

/-- A registered semantic layer for statement variants: what kind of objects the statement
concerns (`ambient`, `omegaModel`, `secondOrderSyntax`, …). **Extensible by registration**,
never a closed enum — higher-order RM, ETF/FSRA, and checked fragments are foreseeable. Kept
distinct from evidence `SemanticScope`: layer classifies the statement's objects; scope says
where a fact relating statements has been established. The two are never silently
identified. -/
structure SemanticLayerId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- A registered semantic layer. -/
structure SemanticLayerEntry where
  /-- The layer identifier. -/
  id : SemanticLayerId
  /-- What statements at this layer concern. -/
  description : String
  deriving Inhabited, Repr, BEq

/-- A problem operation, preserved as shallow metadata (reduction rules arrive after the
Q2–Q5 experiment). One instance and a sequence of instances differ: sequentialization
introduces countable-choice or bar-recursive content. -/
inductive ProblemOp where
  /-- A single instance. -/
  | single
  /-- Finitely many instances in parallel. -/
  | finiteParallelization
  /-- A sequence of instances. -/
  | sequentialization
  deriving Inhabited, Repr, BEq

/-- Stable tag for a problem operation. -/
def ProblemOp.tag : ProblemOp → String
  | .single => "single"
  | .finiteParallelization => "finiteParallelization"
  | .sequentialization => "sequentialization"

/-- An exact statement variant. The parent concept is **explicit data** — never inferred from
the dotted identifier, which is human-facing convention only. A variant may own a Prop-valued
Lean interface (the capability layer); literature-only variants own none. -/
structure StatementVariantEntry where
  /-- The variant identifier. -/
  id : StatementVariantId
  /-- The parent concept, explicit. -/
  concept : ConceptId
  /-- The registered semantic layer. -/
  layer : SemanticLayerId
  /-- The Prop-valued Lean interface, when this variant is capability-owning. Each Lean
  declaration may be owned by at most one variant. -/
  interface? : Option Name := none
  /-- Informal description, including presentation notes (presentation becomes a reusable
  object in the presentations issue). -/
  description : String
  deriving Inhabited, Repr, BEq

/-- A represented uniform problem — deliberately shallow metadata until Q2–Q5 shows what
richer records need. -/
structure UniformProblemEntry where
  /-- The problem identifier. -/
  id : UniformProblemId
  /-- The parent concept, explicit. -/
  concept : ConceptId
  /-- Input representation, prose (a `RepresentationId` arrives with the presentations
  issue). -/
  inputRepresentation : String
  /-- Output representation, prose. -/
  outputRepresentation : String
  /-- Optional Lean interface name (checked against a typed problem schema later). -/
  interface? : Option Name := none
  /-- The problem operation. -/
  operation : ProblemOp := .single
  /-- Minimally-represented `uniformizes` edge: the statement variant this problem
  uniformizes. Evidence-bearing certificates arrive later. -/
  uniformizes? : Option StatementVariantId := none
  deriving Inhabited, Repr, BEq

initialize layerExt : SimplePersistentEnvExtension SemanticLayerEntry
    (Array SemanticLayerEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize variantExt : SimplePersistentEnvExtension StatementVariantEntry
    (Array StatementVariantEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize problemExt : SimplePersistentEnvExtension UniformProblemEntry
    (Array UniformProblemEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

/-- The indexed conceptual catalog with accumulated conflicts. Built by folding every entry
visible in the environment — imported and local — so collisions between independently
developed sibling modules surface in any module that imports both. -/
structure ConceptCatalog where
  /-- All concept entries, in fold order. -/
  concepts : Array ConceptEntry := #[]
  /-- All namespace entries, in fold order. -/
  namespaces : Array ExternalNamespaceEntry := #[]
  /-- All semantic layers, in fold order. -/
  layers : Array SemanticLayerEntry := #[]
  /-- All statement variants, in fold order. -/
  variants : Array StatementVariantEntry := #[]
  /-- All uniform problems, in fold order. -/
  problems : Array UniformProblemEntry := #[]
  /-- All external references, in fold order. -/
  refs : Array ExternalRef := #[]
  /-- The exact-alias resolution map: `(namespace, key) ↦ target`. Direct — no chains. -/
  aliasMap : Std.HashMap (Name × String) CatalogObjectRef := {}
  /-- Lean-interface ownership: each declaration is owned by at most one variant. -/
  interfaceOwner : Std.HashMap Name StatementVariantId := {}
  /-- Accumulated conflicts. A nonempty array poisons every query and export. -/
  conflicts : Array String := #[]

/-- Look up a statement variant by identifier. -/
def ConceptCatalog.findVariant? (cat : ConceptCatalog) (id : Name) :
    Option StatementVariantEntry :=
  cat.variants.find? (·.id.name == id)

/-- Fold the full environment state into an indexed catalog, accumulating conflicts:
duplicate concept ids, duplicate namespace ids, references through unregistered namespaces,
references to unregistered concepts, and exact aliases resolving to two different targets. -/
def ConceptCatalog.ofEnv (env : Environment) : ConceptCatalog := Id.run do
  let mut cat : ConceptCatalog := {}
  let mut conceptIds : NameSet := {}
  let mut nsIds : NameSet := {}
  for c in conceptExt.getState env do
    if conceptIds.contains c.id.name then
      let msg := s!"duplicate concept id '{c.id.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    else
      conceptIds := conceptIds.insert c.id.name
      cat := { cat with concepts := cat.concepts.push c }
  for n in namespaceExt.getState env do
    if nsIds.contains n.id.name then
      let msg := s!"duplicate namespace id '{n.id.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    else
      nsIds := nsIds.insert n.id.name
      cat := { cat with namespaces := cat.namespaces.push n }
  let mut layerIds : NameSet := {}
  for l in layerExt.getState env do
    if layerIds.contains l.id.name then
      let msg := s!"duplicate semantic layer '{l.id.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    else
      layerIds := layerIds.insert l.id.name
      cat := { cat with layers := cat.layers.push l }
  let mut variantIds : NameSet := {}
  for v in variantExt.getState env do
    if variantIds.contains v.id.name then
      let msg := s!"duplicate statement-variant id '{v.id.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    else
      variantIds := variantIds.insert v.id.name
      cat := { cat with variants := cat.variants.push v }
      if !conceptIds.contains v.concept.name then
        let msg := s!"statement variant '{v.id.name}' has unknown parent concept \
          '{v.concept.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
      if !layerIds.contains v.layer.name then
        let msg := s!"statement variant '{v.id.name}' uses unregistered semantic layer \
          '{v.layer.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
      if let some iface := v.interface? then
        match cat.interfaceOwner[iface]? with
        | some owner =>
          let msg := s!"Lean interface '{iface}' is owned by two statement variants \
            ('{owner.name}' and '{v.id.name}')"
          cat := { cat with conflicts := cat.conflicts.push msg }
        | none =>
          cat := { cat with interfaceOwner := cat.interfaceOwner.insert iface v.id }
  let mut problemIds : NameSet := {}
  for q in problemExt.getState env do
    if problemIds.contains q.id.name then
      let msg := s!"duplicate uniform-problem id '{q.id.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    else
      problemIds := problemIds.insert q.id.name
      cat := { cat with problems := cat.problems.push q }
      if !conceptIds.contains q.concept.name then
        let msg := s!"uniform problem '{q.id.name}' has unknown parent concept \
          '{q.concept.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
      if let some u := q.uniformizes? then
        if !variantIds.contains u.name then
          let msg := s!"uniform problem '{q.id.name}' uniformizes unknown statement variant \
            '{u.name}'"
          cat := { cat with conflicts := cat.conflicts.push msg }
  for r in externalRefExt.getState env do
    if !nsIds.contains r.ns.name then
      let msg := s!"reference {r.ns.name}:\"{r.key}\" uses unregistered namespace '{r.ns.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    match r.target with
    | .concept cid =>
      if !conceptIds.contains cid.name then
        let msg := s!"reference {r.ns.name}:\"{r.key}\" targets unregistered concept '{cid.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
    | .statement vid =>
      if !variantIds.contains vid.name then
        let msg := s!"reference {r.ns.name}:\"{r.key}\" targets unregistered statement \
          variant '{vid.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
    | .uniformProblem qid =>
      if !problemIds.contains qid.name then
        let msg := s!"reference {r.ns.name}:\"{r.key}\" targets unregistered uniform \
          problem '{qid.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
    cat := { cat with refs := cat.refs.push r }
    if r.relation == .exactAlias then
      match cat.aliasMap[(r.ns.name, r.key)]? with
      | some existing =>
        if existing != r.target then
          let msg := s!"exact alias {r.ns.name}:\"{r.key}\" resolves to two different \
            targets ('{existing.name}' and '{r.target.name}')"
          cat := { cat with conflicts := cat.conflicts.push msg }
        else
          let msg := s!"exact alias {r.ns.name}:\"{r.key}\" registered twice"
          cat := { cat with conflicts := cat.conflicts.push msg }
      | none =>
        cat := { cat with aliasMap := cat.aliasMap.insert (r.ns.name, r.key) r.target }
  return cat

/-- Reject a conflicted catalog. Every query and export command goes through this gate. -/
def requireCleanCatalog : CommandElabM ConceptCatalog := do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  unless cat.conflicts.isEmpty do
    let lines := "\n  ".intercalate cat.conflicts.toList
    throwError "concept catalog: conflicted state:\n  {lines}"
  return cat

/-! ## Registration commands -/

/-- `rm_namespace id "description"`: register an external namespace. Extensible by
registration — there is deliberately no built-in allowlist. -/
elab "rm_namespace " id:ident descr:str : command => do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  let n := id.getId
  if (namespaceExt.getState (← getEnv)).any (·.id.name == n) then
    throwErrorAt id "concept catalog: duplicate namespace id '{n}'"
  let _ := cat
  modifyEnv fun env => namespaceExt.addEntry env ⟨⟨n⟩, descr.getString⟩

/-- `rm_concept id where description := "…" [label := "…"]`: register a conceptual family.
Deliberately requires no Lean proposition. -/
syntax (name := rmConceptCmd) "rm_concept " ident " where "
  &"description" " := " str (&"label" " := " str)? : command

@[command_elab rmConceptCmd]
def elabRmConcept : CommandElab := fun stx => do
  let id := stx[1].getId
  let description := (⟨stx[5]⟩ : TSyntax `str).getString
  let label := if stx[6].getNumArgs == 0 then toString id
    else (⟨stx[6][2]⟩ : TSyntax `str).getString
  if (conceptExt.getState (← getEnv)).any (·.id.name == id) then
    throwErrorAt stx[1] "concept catalog: duplicate concept id '{id}'"
  modifyEnv fun env => conceptExt.addEntry env ⟨⟨id⟩, description, label⟩

private def parseRelation (stx : Syntax) : CommandElabM ExternalRefRelation :=
  match stx.getId with
  | `exactAlias => pure .exactAlias
  | `sourceLocation => pure .sourceLocation
  | `importedCorrespondence => pure .importedCorrespondence
  | `relatedVariant => pure .relatedVariant
  | r => throwErrorAt stx "concept catalog: unknown relation '{r}' (expected exactAlias | \
      sourceLocation | importedCorrespondence | relatedVariant)"

private def parseTarget (kind tgt : Syntax) : CommandElabM CatalogObjectRef :=
  match kind.getId with
  | `concept => pure (.concept ⟨tgt.getId⟩)
  | `statement => pure (.statement ⟨tgt.getId⟩)
  | `uniformProblem => pure (.uniformProblem ⟨tgt.getId⟩)
  | k => throwErrorAt kind "concept catalog: unknown target kind '{k}' (expected concept | \
      statement | uniformProblem)"

/-- `rm_external_ref ns "key" relation targetKind target`: register a typed external
reference, e.g. `rm_external_ref rmzoo "WKL" exactAlias concept wkl`. -/
elab "rm_external_ref " ns:ident key:str rel:ident kind:ident tgt:ident : command => do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  let nsName := ns.getId
  unless cat.namespaces.any (·.id.name == nsName) do
    throwErrorAt ns "concept catalog: namespace '{nsName}' is not registered \
      (rm_namespace first; namespaces are extensible by registration)"
  let relation ← parseRelation rel
  let target ← parseTarget kind tgt
  match target with
  | .concept cid =>
    unless cat.concepts.any (·.id.name == cid.name) do
      throwErrorAt tgt "concept catalog: unknown concept '{cid.name}'"
  | .statement vid =>
    unless cat.variants.any (·.id.name == vid.name) do
      throwErrorAt tgt "concept catalog: unknown statement variant '{vid.name}'"
  | .uniformProblem qid =>
    unless cat.problems.any (·.id.name == qid.name) do
      throwErrorAt tgt "concept catalog: unknown uniform problem '{qid.name}'"
  if relation == .exactAlias then
    if let some existing := cat.aliasMap[(nsName, key.getString)]? then
      throwErrorAt key "concept catalog: exact alias {nsName}:\"{key.getString}\" already \
        resolves to '{existing.name}'"
  modifyEnv fun env => externalRefExt.addEntry env
    ⟨⟨nsName⟩, key.getString, target, relation⟩

/-- `rm_semantic_layer id "description"`: register a semantic layer. Extensible by
registration; layers classify what a statement's objects are, and are never identified with
evidence scopes. -/
elab "rm_semantic_layer " id:ident descr:str : command => do
  let n := id.getId
  if (layerExt.getState (← getEnv)).any (·.id.name == n) then
    throwErrorAt id "concept catalog: duplicate semantic layer '{n}'"
  modifyEnv fun env => layerExt.addEntry env ⟨⟨n⟩, descr.getString⟩

/-- `rm_statement_variant id where concept := c layer := l [interface := I]
description := "…"`: register an exact statement variant. The parent concept is explicit data,
never inferred from the dotted identifier. An interface must be a Prop-valued declaration
owned by no other variant; literature-only variants omit it. -/
syntax (name := rmVariantCmd) "rm_statement_variant " ident " where "
  &"concept" " := " ident
  &"layer" " := " ident
  (&"interface" " := " ident)?
  &"description" " := " str : command

@[command_elab rmVariantCmd]
def elabRmVariant : CommandElab := fun stx => do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  let id := stx[1].getId
  let conceptName := stx[5].getId
  let layerName := stx[8].getId
  let interfaceStx? := if stx[9].getNumArgs == 0 then none else some stx[9][2]
  let description := (⟨stx[12]⟩ : TSyntax `str).getString
  if cat.variants.any (·.id.name == id) then
    throwErrorAt stx[1] "concept catalog: duplicate statement-variant id '{id}'"
  unless cat.concepts.any (·.id.name == conceptName) do
    throwErrorAt stx[5] "concept catalog: unknown concept '{conceptName}'"
  unless cat.layers.any (·.id.name == layerName) do
    throwErrorAt stx[8] "concept catalog: unregistered semantic layer '{layerName}'"
  let interface? ← interfaceStx?.mapM fun istx => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo istx
    let info ← getConstInfo n
    unless info.type.isProp do
      throwErrorAt istx "concept catalog: interface '{n}' must be a Prop-valued declaration"
    if let some owner := cat.interfaceOwner[n]? then
      throwErrorAt istx "concept catalog: Lean interface '{n}' is already owned by \
        statement variant '{owner.name}'"
    pure n
  modifyEnv fun env => variantExt.addEntry env
    { id := ⟨id⟩, concept := ⟨conceptName⟩, layer := ⟨layerName⟩, interface?, description }

private def parseProblemOp (stx : Syntax) : CommandElabM ProblemOp :=
  match stx.getId with
  | `single => pure .single
  | `finiteParallelization => pure .finiteParallelization
  | `sequentialization => pure .sequentialization
  | o => throwErrorAt stx "concept catalog: unknown problem operation '{o}' (expected \
      single | finiteParallelization | sequentialization)"

/-- `rm_uniform_problem id where concept := c input := "…" output := "…" operation := op
[uniformizes := v]`: register a uniform problem — deliberately shallow metadata until the
Q2–Q5 experiment shows what richer records need. -/
syntax (name := rmProblemCmd) "rm_uniform_problem " ident " where "
  &"concept" " := " ident
  &"input" " := " str
  &"output" " := " str
  &"operation" " := " ident
  (&"uniformizes" " := " ident)? : command

@[command_elab rmProblemCmd]
def elabRmProblem : CommandElab := fun stx => do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  let id := stx[1].getId
  let conceptName := stx[5].getId
  let inputRep := (⟨stx[8]⟩ : TSyntax `str).getString
  let outputRep := (⟨stx[11]⟩ : TSyntax `str).getString
  let operation ← parseProblemOp stx[14]
  let uniformizes? : Option StatementVariantId :=
    if stx[15].getNumArgs == 0 then none else some ⟨stx[15][2].getId⟩
  if cat.problems.any (·.id.name == id) then
    throwErrorAt stx[1] "concept catalog: duplicate uniform-problem id '{id}'"
  unless cat.concepts.any (·.id.name == conceptName) do
    throwErrorAt stx[5] "concept catalog: unknown concept '{conceptName}'"
  if let some u := uniformizes? then
    unless cat.variants.any (·.id.name == u.name) do
      throwErrorAt stx[15][2] "concept catalog: unknown statement variant '{u.name}'"
  modifyEnv fun env => problemExt.addEntry env
    { id := ⟨id⟩, concept := ⟨conceptName⟩, inputRepresentation := inputRep,
      outputRepresentation := outputRep, operation, uniformizes? }

/-! ## Queries (all reject a conflicted state) -/

/-- The canonical serialized form of a concept id. -/
def ConceptId.serialized (c : ConceptId) : String :=
  s!"reverse-mathlib:{c.name}"

/-- The canonical serialized form of a statement-variant id. -/
def StatementVariantId.serialized (v : StatementVariantId) : String :=
  s!"reverse-mathlib:{v.name}"

/-- The canonical serialized form of a uniform-problem id. -/
def UniformProblemId.serialized (q : UniformProblemId) : String :=
  s!"reverse-mathlib:{q.name}"

/-- `#rm_concepts`: list the conceptual catalog. Rejects a conflicted state. -/
elab "#rm_concepts" : command => do
  let cat ← requireCleanCatalog
  let concepts := cat.concepts.qsort fun a b => Name.lt a.id.name b.id.name
  let namespaces := cat.namespaces.qsort fun a b => Name.lt a.id.name b.id.name
  let mut lines := #[s!"concepts ({concepts.size}):"]
  for c in concepts do
    lines := lines.push s!"  {c.id.serialized} — {c.description}"
    let cvars := (cat.variants.filter (·.concept == c.id)).qsort fun a b =>
      Name.lt a.id.name b.id.name
    for v in cvars do
      let iface := match v.interface? with
        | some n => s!" ⟨{n}⟩"
        | none => ""
      lines := lines.push s!"    variant {v.id.serialized} [{v.layer.name}]{iface}"
    let cprobs := (cat.problems.filter (·.concept == c.id)).qsort fun a b =>
      Name.lt a.id.name b.id.name
    for q in cprobs do
      lines := lines.push s!"    problem {q.id.serialized} [{q.operation.tag}]"
    let crefs := cat.refs.filter fun r => r.target == .concept c.id
    for r in (crefs.qsort fun a b =>
        Name.lt a.ns.name b.ns.name || (a.ns.name == b.ns.name && a.key < b.key)) do
      lines := lines.push s!"    {r.ns.name}:\"{r.key}\" [{r.relation.tag}]"
  lines := lines.push s!"namespaces ({namespaces.size}):"
  for n in namespaces do
    lines := lines.push s!"  {n.id.name} — {n.description}"
  logInfo ("\n".intercalate lines.toList)

/-- `#rm_resolve ns "key"`: resolve an external key through the **exact-alias map only** —
provenance relations never participate. Rejects a conflicted state. -/
elab "#rm_resolve " ns:ident key:str : command => do
  let cat ← requireCleanCatalog
  match cat.aliasMap[(ns.getId, key.getString)]? with
  | some (.concept c) => logInfo s!"{ns.getId}:\"{key.getString}\" = {c.serialized}"
  | some t => logInfo s!"{ns.getId}:\"{key.getString}\" = [{t.kindTag}] {t.name}"
  | none => throwErrorAt key "concept catalog: no exact alias for \
      {ns.getId}:\"{key.getString}\" (provenance relations do not resolve)"

end ReverseMathlib.Meta
