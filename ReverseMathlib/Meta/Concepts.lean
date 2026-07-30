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
  /-- Optional **interface schema**: the name of a universe-monomorphic type-valued
  definition giving the expected type of every Lean interface owned by a variant at this
  layer (e.g. an abbreviation unfolding to `OmegaPart → Prop` for a model-indexed layer).
  Candidate interfaces are validated by definitional equality against this type. `none`
  keeps the ambient default: interfaces must be `Prop`-valued — the pre-existing behavior,
  preserved exactly. Ownership is never weakened to "any declaration". -/
  interfaceSchema? : Option Name := none
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

/-! ## Typed facts and contexts (issue #5)

Facts are **catalog data with fail-closed rendering**: a registered fact renders
recorded-but-unsupported until issue #6 links typed evidence; nothing here is inferred true.
Two fact families that never mix: RM facts (implication, equivalence, non-implication,
conservation) whose endpoints are normalized conjunctions of **exact statement variants** and
whose context is a base theory plus a fact scope (distinct fields, never conflated with the
statement's semantic layer); and uniform facts (reducibility, non-reducibility) whose
endpoints are exact uniform problems and whose context is a reducibility notion. No inference
crosses from RM implication to uniform reducibility without a registered bridge theorem. -/

/-- A registered base theory (`rca0`, `rcaOmegaHat`, …) — the theory a theory-context fact is
relative to. Distinct from the statement's semantic layer and from the fact's scope. -/
structure BaseTheoryId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- A registered base theory. -/
structure BaseTheoryEntry where
  /-- The identifier. -/
  id : BaseTheoryId
  /-- What theory this denotes, with citation. -/
  description : String
  deriving Inhabited, Repr, BEq

/-- A registered formula class (`pi11`, `sigma03`, …) parametrizing conservation facts. -/
structure FormulaClassId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- A registered formula class. -/
structure FormulaClassEntry where
  /-- The identifier. -/
  id : FormulaClassId
  /-- Which sentences belong to the class. -/
  description : String
  deriving Inhabited, Repr, BEq

/-- A registered reducibility notion (`weihrauch`, `strongWeihrauch`, `computable`, …) —
extensible by registration, never a closed enum. -/
structure ReducibilityNotionId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- A registered reducibility notion. -/
structure ReducibilityNotionEntry where
  /-- The identifier. -/
  id : ReducibilityNotionId
  /-- Which reducibility this denotes, with citation. -/
  description : String
  deriving Inhabited, Repr, BEq

/-- A typed-fact identifier. -/
structure FactId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

instance : ToString BaseTheoryId := ⟨fun b => toString b.name⟩
instance : ToString FactId := ⟨fun f => toString f.name⟩

/-- Where a theory-context fact is asserted to hold: ordinary provability over the base
theory, ω-model consequence, or all-model consequence — **distinct relations, never
conflated**, and kept separate both from the base theory and from the statements' semantic
layers. -/
inductive FactScope where
  /-- Ordinary provability/consequence over the base theory. -/
  | provability
  /-- Consequence in every ω-model of the base theory. -/
  | omegaModels
  /-- Consequence in every (Henkin/two-sorted) model of the base theory. -/
  | allModels
  deriving Inhabited, Repr, BEq

/-- Stable tag for a fact scope. -/
def FactScope.tag : FactScope → String
  | .provability => "provability"
  | .omegaModels => "omegaModels"
  | .allModels => "allModels"

/-- Mandatory status of a uniform fact (the concordance discipline): `exact` is a genuine
degree claim; `representative` is a descriptive comparison only — never an inference edge;
`variantSensitive` marks a problem not yet specified enough; `notAssigned` is absence of
classification, not evidence of computability or weakness. -/
inductive DegreeStatus where
  /-- A genuine degree/reducibility claim about the exact represented problem. -/
  | exact
  /-- A standard analogue, descriptive only. -/
  | representative
  /-- Representation, promise, output, or sequentialization must be fixed first. -/
  | variantSensitive
  /-- No classification recorded. -/
  | notAssigned
  deriving Inhabited, Repr, BEq

/-- Stable tag for a degree status. -/
def DegreeStatus.tag : DegreeStatus → String
  | .exact => "exact"
  | .representative => "representative"
  | .variantSensitive => "variantSensitive"
  | .notAssigned => "notAssigned"

/-- A normalized conjunction of exact statement variants: sorted by name and deduplicated —
`RT22+COH` is an AST with canonical identity, never a magic string. Endpoints are exact
`StatementVariantId`s; concepts and dotted-name parents are unrepresentable here. -/
structure VariantConjunction where
  /-- The conjuncts — sorted by name, deduplicated (the normalization invariant; construct
  through `normalize`). -/
  variants : Array StatementVariantId
  deriving Inhabited, Repr, BEq

/-- The only intended constructor: sort by name, deduplicate. -/
def VariantConjunction.normalize (vs : Array StatementVariantId) : VariantConjunction :=
  let sorted := vs.qsort fun a b => Name.lt a.name b.name
  ⟨sorted.foldl (init := #[]) fun acc v =>
    if acc.back?.any (· == v) then acc else acc.push v⟩

/-- Canonical rendering: `a+b+c` in normalized order. -/
def VariantConjunction.serialized (c : VariantConjunction) : String :=
  "+".intercalate (c.variants.toList.map (toString ·.name))

/-- The context of a fact. The two families never mix: pairing an RM statement with a uniform
context (or conversely) is a registration error and a fold conflict. -/
inductive FactContext where
  /-- RM-fact context: a base theory and a fact scope, as distinct fields. -/
  | theoryContext (base : BaseTheoryId) (scope : FactScope)
  /-- Uniform-fact context: a reducibility notion. -/
  | uniformContext (notion : ReducibilityNotionId)
  deriving Inhabited, Repr, BEq

/-- Render a fact context compactly. -/
def FactContext.render : FactContext → String
  | .theoryContext b s => s!"theory {b.name} {s.tag}"
  | .uniformContext n => s!"uniform {n.name}"

/-- A typed fact statement. RM endpoints are normalized conjunctions of exact statement
variants; uniform endpoints are exact uniform problems. -/
inductive FactStatement where
  /-- The lhs conjunction implies the rhs conjunction. -/
  | implication (lhs rhs : VariantConjunction)
  /-- The two conjunctions are equivalent. -/
  | equivalence (lhs rhs : VariantConjunction)
  /-- The lhs conjunction does **not** imply the rhs conjunction. -/
  | nonImplication (lhs rhs : VariantConjunction)
  /-- `strong` is `formulaClass`-conservative over `weak`. -/
  | conservation (strong weak : VariantConjunction) (formulaClass : FormulaClassId)
  /-- `strong` is **not** `formulaClass`-conservative over `weak`. -/
  | nonConservation (strong weak : VariantConjunction) (formulaClass : FormulaClassId)
  /-- `lhs` reduces to `rhs` under the context's notion, with mandatory status. -/
  | reducibility (lhs rhs : UniformProblemId) (status : DegreeStatus)
  /-- `lhs` does **not** reduce to `rhs`, with mandatory status. -/
  | nonReducibility (lhs rhs : UniformProblemId) (status : DegreeStatus)
  deriving Inhabited, Repr, BEq

/-- Stable kind tag of a fact statement. -/
def FactStatement.kindTag : FactStatement → String
  | .implication .. => "implication"
  | .equivalence .. => "equivalence"
  | .nonImplication .. => "nonImplication"
  | .conservation .. => "conservation"
  | .nonConservation .. => "nonConservation"
  | .reducibility .. => "reducibility"
  | .nonReducibility .. => "nonReducibility"

/-- Whether the statement belongs to the uniform family. -/
def FactStatement.isUniform : FactStatement → Bool
  | .reducibility .. | .nonReducibility .. => true
  | _ => false

/-- Render a fact statement compactly. -/
def FactStatement.render : FactStatement → String
  | .implication l r => s!"{l.serialized} => {r.serialized}"
  | .equivalence l r => s!"{l.serialized} <=> {r.serialized}"
  | .nonImplication l r => s!"{l.serialized} =/=> {r.serialized}"
  | .conservation s w c => s!"{s.serialized} conservative[{c.name}] over {w.serialized}"
  | .nonConservation s w c => s!"{s.serialized} not-conservative[{c.name}] over {w.serialized}"
  | .reducibility l r st => s!"{l.name} <= {r.name} [{st.tag}]"
  | .nonReducibility l r st => s!"{l.name} </= {r.name} [{st.tag}]"

/-- A registered typed fact: plain catalog data. **Fail-closed**: without linked evidence
(issue #6) a fact renders recorded-but-unsupported and never participates in inference. -/
structure FactEntry where
  /-- The fact identifier. -/
  id : FactId
  /-- The context (theory + scope, or reducibility notion). -/
  context : FactContext
  /-- The typed statement. -/
  statement : FactStatement
  /-- Free-form note (citations live here until #6 links typed provenance). -/
  note : String := ""
  deriving Inhabited, Repr, BEq

initialize baseTheoryExt : SimplePersistentEnvExtension BaseTheoryEntry
    (Array BaseTheoryEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize formulaClassExt : SimplePersistentEnvExtension FormulaClassEntry
    (Array FormulaClassEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize reducibilityNotionExt : SimplePersistentEnvExtension ReducibilityNotionEntry
    (Array ReducibilityNotionEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize factExt : SimplePersistentEnvExtension FactEntry (Array FactEntry) ←
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
  /-- All base theories, in fold order. -/
  baseTheories : Array BaseTheoryEntry := #[]
  /-- All formula classes, in fold order. -/
  formulaClasses : Array FormulaClassEntry := #[]
  /-- All reducibility notions, in fold order. -/
  reducibilityNotions : Array ReducibilityNotionEntry := #[]
  /-- All typed facts, in fold order. -/
  facts : Array FactEntry := #[]
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
  let mut baseIds : NameSet := {}
  for b in baseTheoryExt.getState env do
    if baseIds.contains b.id.name then
      cat := { cat with conflicts := cat.conflicts.push s!"duplicate base theory '{b.id.name}'" }
    else
      baseIds := baseIds.insert b.id.name
      cat := { cat with baseTheories := cat.baseTheories.push b }
  let mut classIds : NameSet := {}
  for c in formulaClassExt.getState env do
    if classIds.contains c.id.name then
      cat := { cat with conflicts := cat.conflicts.push s!"duplicate formula class '{c.id.name}'" }
    else
      classIds := classIds.insert c.id.name
      cat := { cat with formulaClasses := cat.formulaClasses.push c }
  let mut notionIds : NameSet := {}
  for n in reducibilityNotionExt.getState env do
    if notionIds.contains n.id.name then
      let msg := s!"duplicate reducibility notion '{n.id.name}'"
      cat := { cat with conflicts := cat.conflicts.push msg }
    else
      notionIds := notionIds.insert n.id.name
      cat := { cat with reducibilityNotions := cat.reducibilityNotions.push n }
  let mut factIds : NameSet := {}
  for f in factExt.getState env do
    if factIds.contains f.id.name then
      cat := { cat with conflicts := cat.conflicts.push s!"duplicate fact id '{f.id.name}'" }
    else
      factIds := factIds.insert f.id.name
      if let some prior := cat.facts.find? fun g =>
          g.context == f.context && g.statement == f.statement then
        let msg := s!"duplicate fact content: '{f.id.name}' repeats '{prior.id.name}'"
        cat := { cat with conflicts := cat.conflicts.push msg }
      cat := { cat with facts := cat.facts.push f }
      match f.context with
      | .theoryContext b _ =>
        if !baseIds.contains b.name then
          let msg := s!"fact '{f.id.name}' uses unregistered base theory '{b.name}'"
          cat := { cat with conflicts := cat.conflicts.push msg }
        if f.statement.isUniform then
          let msg := s!"fact '{f.id.name}' pairs a uniform statement with a theory context"
          cat := { cat with conflicts := cat.conflicts.push msg }
      | .uniformContext n =>
        if !notionIds.contains n.name then
          let msg := s!"fact '{f.id.name}' uses unregistered reducibility notion '{n.name}'"
          cat := { cat with conflicts := cat.conflicts.push msg }
        if !f.statement.isUniform then
          let msg := s!"fact '{f.id.name}' pairs an RM statement with a uniform context"
          cat := { cat with conflicts := cat.conflicts.push msg }
      let checkVariants (side : String) (c : VariantConjunction) :
          Array String := Id.run do
        let mut msgs := #[]
        if c.variants.isEmpty then
          msgs := msgs.push s!"fact '{f.id.name}' has an empty {side} conjunction"
        for v in c.variants do
          if !variantIds.contains v.name then
            msgs := msgs.push
              s!"fact '{f.id.name}' references unknown statement variant '{v.name}'"
        return msgs
      let checkProblem (q : UniformProblemId) : Array String :=
        if problemIds.contains q.name then #[]
        else #[s!"fact '{f.id.name}' references unknown uniform problem '{q.name}'"]
      let msgs := match f.statement with
        | .implication l r | .equivalence l r | .nonImplication l r =>
          checkVariants "lhs" l ++ checkVariants "rhs" r
        | .conservation s w fc | .nonConservation s w fc =>
          checkVariants "lhs" s ++ checkVariants "rhs" w ++
            (if classIds.contains fc.name then #[]
             else #[s!"fact '{f.id.name}' uses unregistered formula class '{fc.name}'"])
        | .reducibility l r _ | .nonReducibility l r _ =>
          checkProblem l ++ checkProblem r
      cat := { cat with conflicts := cat.conflicts ++ msgs }
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

/-- `rm_semantic_layer id "description" [interfaceSchema := T]`: register a semantic layer.
Extensible by registration; layers classify what a statement's objects are, and are never
identified with evidence scopes. A layer may name an **interface schema** — a
universe-monomorphic type-valued definition giving the expected type of every Lean interface
owned by a variant at this layer; candidate interfaces are checked against it by definitional
equality. Layers without a schema keep the ambient default: interfaces must be
`Prop`-valued. -/
syntax (name := rmLayerCmd) "rm_semantic_layer " ident str
  (&"interfaceSchema" " := " ident)? : command

@[command_elab rmLayerCmd]
def elabRmLayer : CommandElab := fun stx => do
  let id := stx[1].getId
  let descr := (⟨stx[2]⟩ : TSyntax `str).getString
  let schemaStx? := if stx[3].getNumArgs == 0 then none else some stx[3][2]
  if (layerExt.getState (← getEnv)).any (·.id.name == id) then
    throwErrorAt stx[1] "concept catalog: duplicate semantic layer '{id}'"
  let interfaceSchema? ← schemaStx?.mapM fun sstx => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo sstx
    let info ← getConstInfo n
    unless info.levelParams.isEmpty && info.type.isSort do
      throwErrorAt sstx "concept catalog: interface schema '{n}' must be a \
        universe-monomorphic type-valued definition (a name whose type is a Sort)"
    pure n
  modifyEnv fun env => layerExt.addEntry env ⟨⟨id⟩, descr, interfaceSchema?⟩

/-- `rm_statement_variant id where concept := c layer := l [interface := I]
description := "…"`: register an exact statement variant. The parent concept is explicit data,
never inferred from the dotted identifier. An interface must match the registered layer's
interface schema up to definitional equality — `Prop` for layers without a schema — and be
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
  let layerEntry? := cat.layers.find? (·.id.name == layerName)
  let interface? ← interfaceStx?.mapM fun istx => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo istx
    let info ← getConstInfo n
    match layerEntry?.bind (·.interfaceSchema?) with
    | none =>
      -- The ambient default, preserved exactly: schema-less layers demand a Prop.
      unless info.type.isProp do
        throwErrorAt istx "concept catalog: interface '{n}' must be a Prop-valued declaration"
    | some schemaName =>
      let ok ← liftTermElabM <| Meta.isDefEq info.type (Expr.const schemaName [])
      unless ok do
        throwErrorAt istx "concept catalog: interface '{n}' must have type '{schemaName}' \
          (the interface schema of layer '{layerName}') up to definitional equality"
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

/-- `rm_base_theory id "description"`: register a base theory for theory-context facts.
Extensible by registration. -/
elab "rm_base_theory " id:ident descr:str : command => do
  let n := id.getId
  if (baseTheoryExt.getState (← getEnv)).any (·.id.name == n) then
    throwErrorAt id "concept catalog: duplicate base theory '{n}'"
  modifyEnv fun env => baseTheoryExt.addEntry env ⟨⟨n⟩, descr.getString⟩

/-- `rm_formula_class id "description"`: register a formula class for conservation facts.
Extensible by registration. -/
elab "rm_formula_class " id:ident descr:str : command => do
  let n := id.getId
  if (formulaClassExt.getState (← getEnv)).any (·.id.name == n) then
    throwErrorAt id "concept catalog: duplicate formula class '{n}'"
  modifyEnv fun env => formulaClassExt.addEntry env ⟨⟨n⟩, descr.getString⟩

/-- `rm_reducibility_notion id "description"`: register a reducibility notion for uniform
facts. Extensible by registration. -/
elab "rm_reducibility_notion " id:ident descr:str : command => do
  let n := id.getId
  if (reducibilityNotionExt.getState (← getEnv)).any (·.id.name == n) then
    throwErrorAt id "concept catalog: duplicate reducibility notion '{n}'"
  modifyEnv fun env => reducibilityNotionExt.addEntry env ⟨⟨n⟩, descr.getString⟩

private def parseFactScope (stx : Syntax) : CommandElabM FactScope :=
  match stx.getId with
  | `provability => pure .provability
  | `omegaModels => pure .omegaModels
  | `allModels => pure .allModels
  | s => throwErrorAt stx "concept catalog: unknown fact scope '{s}' (expected provability | \
      omegaModels | allModels)"

private def parseDegreeStatus (stx : Syntax) : CommandElabM DegreeStatus :=
  match stx.getId with
  | `exact => pure .exact
  | `representative => pure .representative
  | `variantSensitive => pure .variantSensitive
  | `notAssigned => pure .notAssigned
  | s => throwErrorAt stx "concept catalog: unknown degree status '{s}' (expected exact | \
      representative | variantSensitive | notAssigned)"

/-- `rm_fact id kind where [base := b scope := s] [notion := n status := d]
[formulaClass := c] lhs := [v, …] rhs := [v, …] [note := "…"]`: register a typed fact.

RM kinds (`implication | equivalence | nonImplication | conservation | nonConservation`)
require `base`/`scope` and take normalized conjunctions of **exact statement variants** as
endpoints; conservation kinds additionally require `formulaClass`. Uniform kinds
(`reducibility | nonReducibility`) require `notion`/`status` and take exactly one registered
uniform problem on each side. The two families never mix — stray fields are rejected, not
ignored. Facts are fail-closed data: they render recorded-but-unsupported until issue #6
links typed evidence. -/
syntax (name := rmFactCmd) "rm_fact " ident ident " where "
  (&"base" " := " ident &"scope" " := " ident)?
  (&"notion" " := " ident &"status" " := " ident)?
  (&"formulaClass" " := " ident)?
  &"lhs" " := " "[" ident,* "]"
  &"rhs" " := " "[" ident,* "]"
  (&"note" " := " str)? : command

@[command_elab rmFactCmd]
def elabRmFact : CommandElab := fun stx => do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  let id := stx[1].getId
  let kindStx := stx[2]
  let base? := if stx[4].getNumArgs == 0 then none else some (stx[4][2], stx[4][5])
  let notion? := if stx[5].getNumArgs == 0 then none else some (stx[5][2], stx[5][5])
  let classStx? := if stx[6].getNumArgs == 0 then none else some stx[6][2]
  let lhsStxs := stx[10].getSepArgs
  let rhsStxs := stx[15].getSepArgs
  let note := if stx[17].getNumArgs == 0 then ""
    else (⟨stx[17][2]⟩ : TSyntax `str).getString
  if cat.facts.any (·.id.name == id) then
    throwErrorAt stx[1] "concept catalog: duplicate fact id '{id}'"
  let kind := kindStx.getId
  let isUniformKind := kind == `reducibility || kind == `nonReducibility
  let isConservationKind := kind == `conservation || kind == `nonConservation
  -- Context: exactly the fields the family needs; stray fields are cross-axis errors.
  let context ← do
    if isUniformKind then
      if base?.isSome then
        throwErrorAt kindStx "concept catalog: uniform fact kind '{kind}' takes notion/status, \
          not base/scope — the RM and uniform fact families never mix"
      let some (nstx, _) := notion?
        | throwErrorAt kindStx "concept catalog: uniform fact kind '{kind}' requires \
            notion := … status := …"
      let nname := nstx.getId
      unless cat.reducibilityNotions.any (·.id.name == nname) do
        throwErrorAt nstx "concept catalog: unregistered reducibility notion '{nname}'"
      pure (FactContext.uniformContext ⟨nname⟩)
    else
      if notion?.isSome then
        throwErrorAt kindStx "concept catalog: RM fact kind '{kind}' takes base/scope, not \
          notion/status — the RM and uniform fact families never mix"
      let some (bstx, sstx) := base?
        | throwErrorAt kindStx "concept catalog: RM fact kind '{kind}' requires \
            base := … scope := …"
      let bname := bstx.getId
      unless cat.baseTheories.any (·.id.name == bname) do
        throwErrorAt bstx "concept catalog: unregistered base theory '{bname}'"
      pure (FactContext.theoryContext ⟨bname⟩ (← parseFactScope sstx))
  let mkConj (stxs : Array Syntax) (side : String) :
      CommandElabM VariantConjunction := do
    if stxs.isEmpty then
      throwErrorAt kindStx "concept catalog: the {side} conjunction must name at least one \
        exact statement variant"
    for vstx in stxs do
      unless cat.variants.any (·.id.name == vstx.getId) do
        throwErrorAt vstx "concept catalog: unknown statement variant '{vstx.getId}' — fact \
          endpoints are exact statement variants, never concepts"
    pure (VariantConjunction.normalize (stxs.map fun s => ⟨s.getId⟩))
  let mkProblem (stxs : Array Syntax) (side : String) :
      CommandElabM UniformProblemId := do
    let #[qstx] := stxs
      | throwErrorAt kindStx "concept catalog: the {side} of a uniform fact is exactly one \
          registered uniform problem"
    unless cat.problems.any (·.id.name == qstx.getId) do
      throwErrorAt qstx "concept catalog: unknown uniform problem '{qstx.getId}' — uniform \
        facts relate exact represented problems, never statement variants or concepts"
    pure ⟨qstx.getId⟩
  let mkClass : CommandElabM FormulaClassId := do
    let some cstx := classStx?
      | throwErrorAt kindStx "concept catalog: conservation facts require formulaClass := …"
    unless cat.formulaClasses.any (·.id.name == cstx.getId) do
      throwErrorAt cstx "concept catalog: unregistered formula class '{cstx.getId}'"
    pure ⟨cstx.getId⟩
  if classStx?.isSome && !isConservationKind then
    throwErrorAt kindStx "concept catalog: only conservation facts take formulaClass"
  let statement ← match kind with
    | `implication => pure (FactStatement.implication (← mkConj lhsStxs "lhs")
        (← mkConj rhsStxs "rhs"))
    | `equivalence => pure (FactStatement.equivalence (← mkConj lhsStxs "lhs")
        (← mkConj rhsStxs "rhs"))
    | `nonImplication => pure (FactStatement.nonImplication (← mkConj lhsStxs "lhs")
        (← mkConj rhsStxs "rhs"))
    | `conservation => pure (FactStatement.conservation (← mkConj lhsStxs "lhs")
        (← mkConj rhsStxs "rhs") (← mkClass))
    | `nonConservation => pure (FactStatement.nonConservation (← mkConj lhsStxs "lhs")
        (← mkConj rhsStxs "rhs") (← mkClass))
    | `reducibility => do
        let some (_, dstx) := notion? | throwErrorAt kindStx "unreachable: notion checked"
        pure (FactStatement.reducibility (← mkProblem lhsStxs "lhs")
          (← mkProblem rhsStxs "rhs") (← parseDegreeStatus dstx))
    | `nonReducibility => do
        let some (_, dstx) := notion? | throwErrorAt kindStx "unreachable: notion checked"
        pure (FactStatement.nonReducibility (← mkProblem lhsStxs "lhs")
          (← mkProblem rhsStxs "rhs") (← parseDegreeStatus dstx))
    | k => throwErrorAt kindStx "concept catalog: unknown fact kind '{k}' (expected \
        implication | equivalence | nonImplication | conservation | nonConservation | \
        reducibility | nonReducibility)"
  if let some prior := cat.facts.find? fun g =>
      g.context == context && g.statement == statement then
    throwErrorAt stx[1] "concept catalog: duplicate fact content: this fact is already \
      registered as '{prior.id.name}' (conjunctions compare in normalized form)"
  modifyEnv fun env => factExt.addEntry env { id := ⟨id⟩, context, statement, note }

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

/-- `#rm_facts`: list the typed facts, sorted by id, with contexts and fail-closed evidence
status — every fact renders `recorded, no evidence linked` until issue #6 links typed
evidence. Rejects a conflicted state. -/
elab "#rm_facts" : command => do
  let cat ← requireCleanCatalog
  let facts := cat.facts.qsort fun a b => Name.lt a.id.name b.id.name
  let mut lines := #[s!"facts ({facts.size}):"]
  for f in facts do
    lines := lines.push
      s!"  {f.id.name} [{f.statement.kindTag} | {f.context.render}] \
        {f.statement.render} — recorded, no evidence linked"
    unless f.note.isEmpty do
      lines := lines.push s!"    note: {f.note}"
  let vocab (label : String) (names : Array Name) : String :=
    let sorted := names.qsort Name.lt
    s!"{label} ({sorted.size}): " ++
      (if sorted.isEmpty then "(none)"
       else ", ".intercalate (sorted.toList.map toString))
  lines := lines.push (vocab "base theories" (cat.baseTheories.map (·.id.name)))
  lines := lines.push (vocab "formula classes" (cat.formulaClasses.map (·.id.name)))
  lines := lines.push (vocab "reducibility notions" (cat.reducibilityNotions.map (·.id.name)))
  logInfo ("\n".intercalate lines.toList)

end ReverseMathlib.Meta
