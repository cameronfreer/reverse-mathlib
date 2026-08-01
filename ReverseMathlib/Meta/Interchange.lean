/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Concepts

/-!
# External-catalog interchange: imported reduction records (issue #28)

The contract-first interchange channel between this catalog and an external
computable-analysis catalog. **No Lean dependency in either direction**: the external
repository owns the machine model (representations, problems, realizers, the reducibility
relations); this side ingests a **versioned canonical JSON** file of reduction records and
stores them as typed *imported evidence* — never Lean axioms, never certified facts, never
edges in any other fact family.

## The JSON contract, version `rmlib-ca-interchange/1`

```json
{ "schema": "rmlib-ca-interchange/1",
  "source": { "repository": "<owner/repo>", "revision": "<40-hex git commit>" },
  "namespace": "<registered rm_namespace id>",
  "reductions": [
    { "id": "<file-unique record id>",
      "notion": "<external reducibility-notion key>",
      "lhs": { "problem": "<external problem id>", "presentation": "<presentation id>" },
      "rhs": { "problem": "<external problem id>", "presentation": "<presentation id>" },
      "degree": "exact | representative | variantSensitive | notAssigned",
      "status": "importedChecked | reported",
      "theorem": "<fully qualified source theorem>",
      "mechanism": "<checking mechanism, e.g. lean-kernel>",
      "note": "<optional>" } ] }
```

## Resolution: named crosswalks, never identity by matching strings

Every external identifier resolves through a **registered exact alias** in the named
namespace (`rm_external_ref … exactAlias …`), or ingestion fails:

* the notion key must resolve to a registered reducibility notion
  (`rm_external_ref ns "<notion>" exactAlias reducibilityNotion <id>`);
* each endpoint's composite key `<problem>/<presentation>` must resolve to a registered
  represented uniform problem
  (`rm_external_ref ns "<problem>/<presentation>" exactAlias uniformProblem <id>`).

An alias resolving to any *other* catalog object kind is a hard error — imported
reductions relate represented uniform problems only, so a record can never cross into the
concept, statement-variant, or RM fact families.

## Trust and fail-closed discipline

`importedChecked` is accepted only when **all** trust fields are present and validated:
the source repository, a 40-hex pinned revision, the source theorem name, and the checking
mechanism. A record claiming `importedChecked` with incomplete trust data is ingested as
`reported`, with the downgrade reason displayed. Everything else fails closed: unknown
schema versions, unregistered namespaces, unresolvable or wrong-kind aliases, unknown
degree or status tags, duplicate record ids, and malformed JSON are hard errors.

Imported records live in their own environment extension and are displayed by
`#rm_imports`. They enter no certified count: the `#revmath_stats` scoreboard is
structurally out of reach.
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- The accepted interchange schema version. Extending the schema means adding a version
here and keeping this one readable — never silently reinterpreting existing files. -/
def interchangeSchemaV1 : String := "rmlib-ca-interchange/1"

/-- The trust status of an imported record. -/
inductive ImportedStatus where
  /-- Externally checked, with all trust fields present and validated. -/
  | importedChecked
  /-- Reported without complete validated trust data. Displayed, never trusted further. -/
  | reported
  deriving Inhabited, Repr, BEq

/-- Stable tag for an imported-record status. -/
def ImportedStatus.tag : ImportedStatus → String
  | .importedChecked => "importedChecked"
  | .reported => "reported"

/-- A typed imported reduction record: the external identifiers, the crosswalk-resolved
local objects, the explicit source coordinates, and the validated trust status. -/
structure ImportedReductionEntry where
  /-- The file-unique external record id. -/
  id : String
  /-- The registered namespace the record's keys resolve through. -/
  ns : ExternalNamespaceId
  /-- The source repository (`owner/repo`). -/
  repository : String
  /-- The pinned source revision (40-hex git commit). -/
  revision : String
  /-- The external reducibility-notion key. -/
  notionKey : String
  /-- The crosswalk-resolved local reducibility notion. -/
  notion : ReducibilityNotionId
  /-- The external lhs composite key (`problem/presentation`). -/
  lhsKey : String
  /-- The crosswalk-resolved local lhs problem. -/
  lhs : UniformProblemId
  /-- The external rhs composite key (`problem/presentation`). -/
  rhsKey : String
  /-- The crosswalk-resolved local rhs problem. -/
  rhs : UniformProblemId
  /-- The degree status, in the concordance discipline. -/
  degree : DegreeStatus
  /-- The validated trust status. -/
  status : ImportedStatus
  /-- The source theorem name, when supplied. -/
  theoremName? : Option String := none
  /-- The checking mechanism, when supplied. -/
  mechanism? : Option String := none
  /-- Why a claimed `importedChecked` was downgraded to `reported`, if it was. -/
  downgraded? : Option String := none
  /-- Optional free-text note. -/
  note : String := ""
  deriving Inhabited, Repr, BEq

initialize importedReductionExt :
    SimplePersistentEnvExtension ImportedReductionEntry (Array ImportedReductionEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

/-- Read a mandatory string field, with a precise error. -/
private def getStrField (j : Json) (field : String) (ctx : String) :
    CommandElabM String := do
  match j.getObjVal? field with
  | .error _ => throwError "interchange: {ctx}: missing field '{field}'"
  | .ok v => match v.getStr? with
    | .error _ => throwError "interchange: {ctx}: field '{field}' must be a string"
    | .ok s => pure s

/-- Read an optional string field (absent is fine; a non-string value is malformed). -/
private def getStrField? (j : Json) (field : String) (ctx : String) :
    CommandElabM (Option String) := do
  match j.getObjVal? field with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .error _ => throwError "interchange: {ctx}: field '{field}' must be a string"
    | .ok s => pure (some s)

/-- Read a mandatory object-valued field. -/
private def getObjField (j : Json) (field : String) (ctx : String) :
    CommandElabM Json := do
  match j.getObjVal? field with
  | .error _ => throwError "interchange: {ctx}: missing field '{field}'"
  | .ok v => pure v

/-- A 40-character lowercase-hex pinned git revision. -/
private def isPinnedRevision (s : String) : Bool :=
  s.length == 40 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Parse a degree tag, fail-closed. -/
private def parseDegree (s ctx : String) : CommandElabM DegreeStatus :=
  match s with
  | "exact" => pure .exact
  | "representative" => pure .representative
  | "variantSensitive" => pure .variantSensitive
  | "notAssigned" => pure .notAssigned
  | _ => throwError "interchange: {ctx}: unknown degree '{s}' (expected exact | \
      representative | variantSensitive | notAssigned)"

/-- Resolve an endpoint's composite key to a registered uniform problem through the
exact-alias map — wrong-kind targets are the cross-family error. -/
private def resolveProblem (cat : ConceptCatalog) (nsName : Name) (key ctx : String) :
    CommandElabM UniformProblemId := do
  match cat.aliasMap[(nsName, key)]? with
  | some (.uniformProblem q) => pure q
  | some t => throwError "interchange: {ctx}: alias {nsName}:\"{key}\" resolves to \
      {t.kindTag} '{t.name}' — imported reductions relate represented uniform problems \
      only, never objects of another fact family"
  | none => throwError "interchange: {ctx}: no registered crosswalk for endpoint \
      {nsName}:\"{key}\" (register rm_external_ref … exactAlias uniformProblem … first; \
      identity is never inferred by matching strings)"

/-- Parse and validate one reduction record. -/
private def parseRecord (cat : ConceptCatalog) (nsName : Name)
    (repository revision : String) (trustSource? : Option String) (j : Json) :
    CommandElabM ImportedReductionEntry := do
  let id ← getStrField j "id" "reduction record"
  let ctx := s!"record '{id}'"
  let notionKey ← getStrField j "notion" ctx
  let notion ← match cat.aliasMap[(nsName, notionKey)]? with
    | some (.reducibilityNotion n) => pure n
    | some t => throwError "interchange: {ctx}: alias {nsName}:\"{notionKey}\" resolves \
        to {t.kindTag} '{t.name}', not a reducibility notion"
    | none => throwError "interchange: {ctx}: no registered crosswalk for reducibility \
        notion {nsName}:\"{notionKey}\" (register rm_external_ref … exactAlias \
        reducibilityNotion … first)"
  let readEndpoint (side : String) : CommandElabM (String × UniformProblemId) := do
    let e ← getObjField j side ctx
    let p ← getStrField e "problem" s!"{ctx} {side}"
    let pres ← getStrField e "presentation" s!"{ctx} {side}"
    if p.isEmpty || pres.isEmpty then
      throwError "interchange: {ctx} {side}: problem and presentation ids must be nonempty"
    let key := s!"{p}/{pres}"
    pure (key, ← resolveProblem cat nsName key s!"{ctx} {side}")
  let (lhsKey, lhs) ← readEndpoint "lhs"
  let (rhsKey, rhs) ← readEndpoint "rhs"
  let degree ← parseDegree (← getStrField j "degree" ctx) ctx
  let statusStr ← getStrField j "status" ctx
  let theoremName? ← getStrField? j "theorem" ctx
  let mechanism? ← getStrField? j "mechanism" ctx
  let note := (← getStrField? j "note" ctx).getD ""
  let (status, downgraded?) ← match statusStr with
    | "reported" => pure (ImportedStatus.reported, none)
    | "importedChecked" => do
      let missing := #[]
        |>.append (if trustSource?.isSome then #[trustSource?.get!] else #[])
        |>.append (if theoremName?.isNone then #["theorem"] else #[])
        |>.append (if mechanism?.isNone then #["mechanism"] else #[])
      if missing.isEmpty then
        pure (ImportedStatus.importedChecked, none)
      else
        pure (ImportedStatus.reported,
          some s!"claimed importedChecked without validated trust data \
            ({", ".intercalate missing.toList})")
    | s => throwError "interchange: {ctx}: unknown status '{s}' (expected \
        importedChecked | reported)"
  pure { id, ns := ⟨nsName⟩, repository, revision, notionKey, notion, lhsKey, lhs,
         rhsKey, rhs, degree, status, theoremName?, mechanism?, downgraded?, note }

/-- `rm_import_reductions "path.json"`: ingest a versioned interchange file of external
reduction records. Fail-closed throughout; a record claiming `importedChecked` without
complete validated trust data is ingested as `reported` with the reason recorded. -/
elab "rm_import_reductions " path:str : command => do
  let cat ← requireCleanCatalog
  let content ← try liftM (IO.FS.readFile ⟨path.getString⟩)
    catch e => throwErrorAt path "interchange: cannot read '{path.getString}': {e.toMessageData}"
  let json ← match Json.parse content with
    | .error e => throwErrorAt path "interchange: '{path.getString}' is not valid JSON: {e}"
    | .ok j => pure j
  let schema ← getStrField json "schema" "interchange file"
  unless schema == interchangeSchemaV1 do
    throwErrorAt path "interchange: unknown schema version '{schema}' (this reader accepts \
      '{interchangeSchemaV1}'); schema changes are versioned, never silently reinterpreted"
  let source ← getObjField json "source" "interchange file"
  let repository ← getStrField source "repository" "interchange source"
  let revision ← getStrField source "revision" "interchange source"
  let nsStr ← getStrField json "namespace" "interchange file"
  let nsName := nsStr.toName
  unless cat.namespaces.any (·.id.name == nsName) do
    throwErrorAt path "interchange: namespace '{nsStr}' is not registered (rm_namespace \
      first; namespaces are extensible by registration)"
  -- File-level trust validation, reported per record as a downgrade reason.
  let trustSource? : Option String :=
    if repository.isEmpty then some "repository"
    else if !isPinnedRevision revision then some "pinned 40-hex revision"
    else none
  let reductions ← match json.getObjVal? "reductions" with
    | .error _ => throwErrorAt path "interchange: interchange file: missing field 'reductions'"
    | .ok v => match v.getArr? with
      | .error _ => throwErrorAt path "interchange: field 'reductions' must be an array"
      | .ok a => pure a
  let existing := (importedReductionExt.getState (← getEnv)).map (·.id)
  let mut seen : Std.HashSet String := {}
  for r in reductions do
    let entry ← parseRecord cat nsName repository revision trustSource? r
    if seen.contains entry.id || existing.contains entry.id then
      throwErrorAt path "interchange: duplicate imported record id '{entry.id}'"
    seen := seen.insert entry.id
    modifyEnv fun env => importedReductionExt.addEntry env entry

/-- `#rm_imports`: display the imported reduction records, sorted by id. External evidence
only — never axioms, never certified counts, never cross-family edges. -/
elab "#rm_imports" : command => do
  let _ ← requireCleanCatalog
  let entries := (importedReductionExt.getState (← getEnv)).qsort fun a b => a.id < b.id
  let mut lines := #[s!"imported reductions ({entries.size}) — external evidence: never \
    axioms, no certified counts, no cross-family edges:"]
  for e in entries do
    lines := lines.push
      s!"  {e.ns.name}:\"{e.id}\" [{e.notion.name}, {e.degree.tag}] {e.lhs.name} <= \
        {e.rhs.name} — {e.status.tag}"
    lines := lines.push s!"    external: {e.lhsKey} <= {e.rhsKey} [notion {e.notionKey}]"
    lines := lines.push s!"    source: {e.repository} @ {e.revision}"
    match e.theoremName?, e.mechanism? with
    | some t, some m => lines := lines.push s!"    theorem: {t}; mechanism: {m}"
    | some t, none => lines := lines.push s!"    theorem: {t}; mechanism: (none)"
    | none, some m => lines := lines.push s!"    theorem: (none); mechanism: {m}"
    | none, none => pure ()
    if let some reason := e.downgraded? then
      lines := lines.push s!"    downgraded: {reason}"
    unless e.note.isEmpty do
      lines := lines.push s!"    note: {e.note}"
  logInfo ("\n".intercalate lines.toList)

end ReverseMathlib.Meta
