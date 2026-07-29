/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry

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

/-- The indexed conceptual catalog with accumulated conflicts. Built by folding every entry
visible in the environment — imported and local — so collisions between independently
developed sibling modules surface in any module that imports both. -/
structure ConceptCatalog where
  /-- All concept entries, in fold order. -/
  concepts : Array ConceptEntry := #[]
  /-- All namespace entries, in fold order. -/
  namespaces : Array ExternalNamespaceEntry := #[]
  /-- All external references, in fold order. -/
  refs : Array ExternalRef := #[]
  /-- The exact-alias resolution map: `(namespace, key) ↦ target`. Direct — no chains. -/
  aliasMap : Std.HashMap (Name × String) CatalogObjectRef := {}
  /-- Accumulated conflicts. A nonempty array poisons every query and export. -/
  conflicts : Array String := #[]

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
  for r in externalRefExt.getState env do
    if !nsIds.contains r.ns.name then
      let msg := s!"reference {r.ns.name}:\"{r.key}\" uses unregistered namespace '{r.ns.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    if let .concept cid := r.target then
      if !conceptIds.contains cid.name then
        let msg := s!"reference {r.ns.name}:\"{r.key}\" targets unregistered concept '{cid.name}'"
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
  | `statement => throwErrorAt kind "concept catalog: statement-variant targets arrive with \
      issue #4"
  | `uniformProblem => throwErrorAt kind "concept catalog: uniform-problem targets arrive \
      with issue #4"
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
  if let .concept cid := target then
    unless cat.concepts.any (·.id.name == cid.name) do
      throwErrorAt tgt "concept catalog: unknown concept '{cid.name}'"
  if relation == .exactAlias then
    if let some existing := cat.aliasMap[(nsName, key.getString)]? then
      throwErrorAt key "concept catalog: exact alias {nsName}:\"{key.getString}\" already \
        resolves to '{existing.name}'"
  modifyEnv fun env => externalRefExt.addEntry env
    ⟨⟨nsName⟩, key.getString, target, relation⟩

/-! ## Queries (all reject a conflicted state) -/

/-- The canonical serialized form of a concept id. -/
def ConceptId.serialized (c : ConceptId) : String :=
  s!"reverse-mathlib:{c.name}"

/-- `#rm_concepts`: list the conceptual catalog. Rejects a conflicted state. -/
elab "#rm_concepts" : command => do
  let cat ← requireCleanCatalog
  let concepts := cat.concepts.qsort fun a b => Name.lt a.id.name b.id.name
  let namespaces := cat.namespaces.qsort fun a b => Name.lt a.id.name b.id.name
  let mut lines := #[s!"concepts ({concepts.size}):"]
  for c in concepts do
    lines := lines.push s!"  {c.id.serialized} — {c.description}"
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
