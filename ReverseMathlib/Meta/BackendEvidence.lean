/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Interchange
import ReverseMathlib.Meta.InterfaceEncoder
import ReverseMathlib.Meta.Registry

/-!
# Backend-evidence ingestion: `rmlib-bridge-evidence/1`

The contract-first channel by which an external checked backend (the
reverse-mathlib-foundation ω-semantics bridge) is ingested as **backend evidence** — a
fourth evidence grade, stored in its own extension apart from certified facts, imported
reductions, and reported corpus findings. **No Lean dependency in either direction**;
the backend repository owns its theorems, this side ingests a versioned canonical JSON
file (deterministic fixed-order serialization; this reader never depends on key order).
Contract: reverse-mathlib-foundation `docs/evidence-schema.md`.

Four record kinds, kept permanently distinct: **context realization** (one-way — a
realization licenses per-context readings only, never unrestricted semantic base-theory
claims), **statement adapters** (unconditional, tying an external sentence to a
registered local variant's exact interface), **calculus identity** (a backend-local
calculus with its soundness theorem and a pending standard-calculus comparison), and
**calculus-relative nonderivability** (typed references to its calculus and adapter
records; rendered only with its calculus and comparison qualifiers).

## Resolution and semantic anchors

External keys resolve through registered exact aliases only; different kinds resolve to
different local object kinds (`contextKey` → semantic context, `variantKey` → statement
variant; calculus records are backend-local and carry no alias). After resolution the
semantic anchors are verified by exact declaration identity: the resolved context's
`contextDecl` must be the record's declared context predicate, and the resolved
variant's `interface` must be the record's declared capability.

## Fingerprints

The file's `lean-interface-expr/1` manifest is recomputed from the **resolved local
roots** (the context predicates and variant interfaces) over this repository's own
elaborated environment: the covered-name set and every canonical payload must match
exactly. Missing, extra, or mismatched declarations are hard failures regardless of
claimed status — an under-covered manifest is rejected whole. Backend revision drift is
therefore acceptable exactly when the semantic interface is unchanged.

## Trust

Hard failures, never downgrades: unknown schema or fingerprint-schema version,
unregistered namespace, unknown kind or tag, malformed or non-40-hex revisions,
wrong-kind aliases, failed semantic anchors, broken or inconsistent typed record
references, duplicate ids, malformed JSON, and any fingerprint failure. Downgrades to
`reported` with a visible reason: a Lean-toolchain or mathlib-revision mismatch with
this workspace (the fingerprint closure deliberately excludes non-local bodies, so
`backendChecked` is unavailable across a toolchain gap), and incomplete checking
coordinates (missing theorem, mechanism, audit, or a nonstandard axiom list).

Backend records enter no certified count, no port, no closure edge, and no
concept-strength graph edge; they are exported and rendered as their own section.
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- The accepted backend-evidence schema version. -/
def backendEvidenceSchemaV2 : String := "rmlib-bridge-evidence/2"

/-- The accepted fingerprint-schema version. -/
def fingerprintSchemaV1 : String := "lean-interface-expr/1"

/-- The trust status of a backend-evidence record. -/
inductive BackendStatus where
  /-- Externally kernel-checked with validated trust data, matching toolchain
  coordinates, and an exactly-matching interface manifest. -/
  | backendChecked
  /-- Recorded without complete validated trust data or across a toolchain gap.
  Displayed with its reason, never trusted further. -/
  | reported
  deriving Inhabited, Repr, BEq

/-- Stable tag for a backend-evidence status. -/
def BackendStatus.tag : BackendStatus → String
  | .backendChecked => "backendChecked"
  | .reported => "reported"

/-- Kind-specific payload of a backend-evidence record. The five kinds are permanently
distinct; scope discipline lives in the rendering functions, which are generated from
these typed fields. -/
inductive BackendRecordData where
  /-- One-way context realization: the backend theory is realized at the resolved
  semantic context. Never a context equivalence. -/
  | contextRealization (theory : String) (contextKey : String)
      (context : SemanticContextId) (contextPred : Name)
      (direction : String) (realizationStatus : String)
  /-- Unconditional statement adapter: the backend sentence's satisfaction is exactly
  the resolved variant's interface. -/
  | statementAdapter (sentence : String) (capability : Name)
      (variantKey : String) (variant : StatementVariantId) (adapterStatus : String)
  /-- Backend-local calculus identity, with its soundness theorem and its
  standard-calculus comparison status. -/
  | calculusIdentity (calculusId : String) (derivability : String)
      (soundness : String) (standardComparison : String)
  /-- Calculus-relative nonderivability, referencing its calculus and adapter records
  by id. -/
  | calculusNonderivability (calculusRecord : String) (sentenceAdapter : String)
      (calculusId : String) (theory : String) (sentence : String)
  /-- All-model semantic countermodel: the backend theory does not semantically imply
  the backend sentence over the general model class. References are identity checks
  only — neither licenses an all-model adapter to any local capability. -/
  | semanticCountermodel (contextRealization : String) (sentenceAdapter : String)
      (theory : String) (sentence : String) (scope : String) (modelClass : String)
      (witnessProvenance : String) (witnessBase : String)
  deriving Inhabited, Repr, BEq

/-- Stable kind tag. -/
def BackendRecordData.kindTag : BackendRecordData → String
  | .contextRealization .. => "contextRealization"
  | .statementAdapter .. => "statementAdapter"
  | .calculusIdentity .. => "calculusIdentity"
  | .calculusNonderivability .. => "calculusNonderivability"
  | .semanticCountermodel .. => "semanticCountermodel"

/-- A typed backend-evidence record: source coordinates, trust status, and the
kind-specific payload. -/
structure BackendEvidenceEntry where
  /-- The file-unique record id. -/
  id : String
  /-- The registered namespace the record's keys resolve through. -/
  ns : ExternalNamespaceId
  /-- The source repository (`owner/repo`). -/
  repository : String
  /-- The backend **export/check** revision (40-hex): the commit at which the emitter
  ran and the artifact's fingerprints were checked — the artifact's embedded
  `source.revision`. -/
  revision : String
  /-- The backend **artifact-publishing** revision (40-hex): the commit whose tree
  contains this artifact byte-for-byte. Distinct from `revision` by self-reference:
  the artifact cannot be committed at the revision it records. Supplied externally at
  the ingestion site. -/
  artifactRevision : String
  /-- The repository-relative path of the vendored artifact, linking the canonical
  export back to the raw ingested bytes. -/
  artifactPath : String
  /-- The backend's checked revision of this repository (40-hex). -/
  rmRevision : String
  /-- The backend's Foundation dependency revision (40-hex). -/
  foundationRevision : String
  /-- The backend's mathlib dependency revision (40-hex). -/
  mathlibRevision : String
  /-- The backend toolchain. -/
  toolchain : String
  /-- The declared checking mechanism, when validly supplied. -/
  mechanism? : Option String
  /-- The declared audit entry point, when validly supplied. -/
  audit? : Option String
  /-- The declared allowed-axiom list, as supplied. -/
  allowedAxioms : Array String
  /-- The exported record constant on the backend side. -/
  exportName : String
  /-- The backing theorem, when the kind carries one (empty strings count as
  missing). -/
  theoremName? : Option String
  /-- The validated trust status. -/
  status : BackendStatus
  /-- Why a claimed `backendChecked` was downgraded to `reported`, if it was. -/
  downgraded? : Option String
  /-- The kind-specific payload. -/
  data : BackendRecordData
  deriving Inhabited, Repr, BEq

initialize backendEvidenceExt :
    SimplePersistentEnvExtension BackendEvidenceEntry (Array BackendEvidenceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

namespace BackendEvidence

/-- Read a mandatory string field. -/
private def getStr (j : Json) (field ctx : String) : CommandElabM String := do
  match j.getObjVal? field with
  | .error _ => throwError "backend evidence: {ctx}: missing field '{field}'"
  | .ok v => match v.getStr? with
    | .error _ => throwError "backend evidence: {ctx}: field '{field}' must be a string"
    | .ok s => pure s

/-- Read an optional string field (absent is fine; a non-string value is malformed). -/
private def getStr? (j : Json) (field ctx : String) : CommandElabM (Option String) := do
  match j.getObjVal? field with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .error _ => throwError "backend evidence: {ctx}: field '{field}' must be a string"
    | .ok s => pure (some s)

private def getObj (j : Json) (field ctx : String) : CommandElabM Json := do
  match j.getObjVal? field with
  | .error _ => throwError "backend evidence: {ctx}: missing field '{field}'"
  | .ok v => pure v

private def getArr (j : Json) (field ctx : String) : CommandElabM (Array Json) := do
  match j.getObjVal? field with
  | .error _ => throwError "backend evidence: {ctx}: missing field '{field}'"
  | .ok v => match v.getArr? with
    | .error _ => throwError "backend evidence: {ctx}: field '{field}' must be an array"
    | .ok a => pure a

/-- A 40-character lowercase-hex pinned git revision; malformed revisions are hard
failures. -/
private def requireRevision (s : String) (ctx : String) : CommandElabM String := do
  unless s.length == 40 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throwError "backend evidence: {ctx}: '{s}' is not a full lowercase 40-hex revision"
  pure s

/-- The standard axiom names; a backend claiming anything else is not `leanKernel`
checking in this project's sense. -/
private def standardAxioms : List String :=
  ["Classical.choice", "Quot.sound", "propext"]

/-- The parsed checking block plus its incomplete-coordinate reasons (downgrade, never
hard failure): missing checking block, unrecognized or empty mechanism, missing / empty
/ non-string audit, or a nonstandard axiom list. Empty strings count as missing —
malformed trust coordinates must never become `backendChecked`. -/
private structure CheckingData where
  reasons : Array String
  mechanism? : Option String
  audit? : Option String
  allowedAxioms : Array String

private def parseChecking (json : Json) : CheckingData := Id.run do
  let mut reasons : Array String := #[]
  let .ok checking := json.getObjVal? "checking"
    | return ⟨#["missing checking block"], none, none, #[]⟩
  let mechanism? ← do
    match checking.getObjVal? "mechanism" with
    | .error _ =>
      reasons := reasons.push "missing checking mechanism"
      pure none
    | .ok v => match v.getStr? with
      | .error _ =>
        reasons := reasons.push "malformed checking mechanism (not a string)"
        pure none
      | .ok "leanKernel" => pure (some "leanKernel")
      | .ok "" =>
        reasons := reasons.push "empty checking mechanism"
        pure none
      | .ok m =>
        reasons := reasons.push s!"unrecognized checking mechanism '{m}'"
        pure (some m)
  let audit? ← do
    match checking.getObjVal? "audit" with
    | .error _ =>
      reasons := reasons.push "missing checking audit"
      pure none
    | .ok v => match v.getStr? with
      | .error _ =>
        reasons := reasons.push "malformed checking audit (not a string)"
        pure none
      | .ok "" =>
        reasons := reasons.push "empty checking audit"
        pure none
      | .ok a => pure (some a)
  let mut allowedAxioms : Array String := #[]
  match (checking.getObjValAs? (Array Json) "allowedAxioms").toOption with
  | some axs =>
    for a in axs do
      match a.getStr? with
      | .ok s =>
        allowedAxioms := allowedAxioms.push s
        if !standardAxioms.contains s then
          reasons := reasons.push s!"nonstandard axiom '{s}'"
      | .error _ => reasons := reasons.push "malformed allowedAxioms entry"
  | none => reasons := reasons.push "missing or malformed allowedAxioms"
  return ⟨reasons, mechanism?, audit?, allowedAxioms⟩

/-- Empty strings count as absent trust coordinates. -/
private def nonempty? (s? : Option String) : Option String :=
  match s? with
  | some "" => none
  | v => v

/-- Resolve an external key to a registered semantic context — wrong-kind targets are
the cross-family hard error. -/
private def resolveContext (cat : ConceptCatalog) (nsName : Name) (key ctx : String) :
    CommandElabM SemanticContextEntry := do
  match cat.aliasMap[(nsName, key)]? with
  | some (.semanticContext c) =>
    match cat.semanticContexts.find? (·.id.name == c.name) with
    | some entry => pure entry
    | none => throwError "backend evidence: {ctx}: alias resolves to unregistered \
        semantic context '{c.name}'"
  | some t => throwError "backend evidence: {ctx}: alias {nsName}:\"{key}\" resolves to \
      {t.kindTag} '{t.name}' — context realizations target registered semantic contexts \
      only, never objects of another kind"
  | none => throwError "backend evidence: {ctx}: no registered crosswalk for context \
      {nsName}:\"{key}\" (register rm_external_ref … exactAlias semanticContext … first; \
      identity is never inferred by matching strings)"

/-- Resolve an external key to a registered statement variant. -/
private def resolveVariant (cat : ConceptCatalog) (nsName : Name) (key ctx : String) :
    CommandElabM StatementVariantEntry := do
  match cat.aliasMap[(nsName, key)]? with
  | some (.statement v) =>
    match cat.variants.find? (·.id.name == v.name) with
    | some entry => pure entry
    | none => throwError "backend evidence: {ctx}: alias resolves to unregistered \
        statement variant '{v.name}'"
  | some t => throwError "backend evidence: {ctx}: alias {nsName}:\"{key}\" resolves to \
      {t.kindTag} '{t.name}' — statement adapters target registered statement variants \
      only, never objects of another kind"
  | none => throwError "backend evidence: {ctx}: no registered crosswalk for variant \
      {nsName}:\"{key}\" (register rm_external_ref … exactAlias statement … first; \
      identity is never inferred by matching strings)"

/-- Phase-1 parse result: the record before crosswalk resolution and reference
checking. -/
private structure ParsedRecord where
  id : String
  kind : String
  exportName : String
  claimedStatus : String
  theoremName? : Option String
  json : Json

/-- Phase 1: structural parse of one record — id, kind, claimed status; kind-specific
fields are read in phase 2. Unknown kinds and status tags are hard failures. -/
private def parseRecordShell (j : Json) : CommandElabM ParsedRecord := do
  let id ← getStr j "id" "backend record"
  let ctx := s!"record '{id}'"
  let kind ← getStr j "kind" ctx
  unless ["contextRealization", "statementAdapter", "calculusIdentity",
      "calculusNonderivability", "semanticCountermodel"].contains kind do
    throwError "backend evidence: {ctx}: unknown kind '{kind}'"
  let claimedStatus ← getStr j "status" ctx
  unless ["backendChecked", "reported"].contains claimedStatus do
    throwError "backend evidence: {ctx}: unknown status '{claimedStatus}' (expected \
      backendChecked | reported)"
  let exportName ← getStr j "export" ctx
  let theoremName? ← getStr? j "theorem" ctx
  pure { id, kind, exportName, claimedStatus, theoremName?, json := j }

/-- Phase 2+3 result: the typed payload plus this record's fingerprint roots. -/
private structure ResolvedRecord where
  shell : ParsedRecord
  data : BackendRecordData
  roots : List Name

/-- Phase 2: kind-specific fields, crosswalk resolution, and semantic anchors. -/
private def resolveRecord (cat : ConceptCatalog) (nsName : Name) (p : ParsedRecord) :
    CommandElabM ResolvedRecord := do
  let j := p.json
  let ctx := s!"record '{p.id}'"
  match p.kind with
  | "contextRealization" => do
    let theory ← getStr j "theory" ctx
    let contextKey ← getStr j "contextKey" ctx
    let contextPredStr ← getStr j "context" ctx
    let direction ← getStr j "direction" ctx
    unless direction == "forward" do
      throwError "backend evidence: {ctx}: unknown direction '{direction}' (this \
        family records one-way realizations; only 'forward' exists)"
    let realizationStatus ← getStr j "realizationStatus" ctx
    unless realizationStatus == "realizationOnly" do
      throwError "backend evidence: {ctx}: unknown realizationStatus \
        '{realizationStatus}' (only 'realizationOnly' exists — realization evidence is \
        never context equivalence)"
    let entry ← resolveContext cat nsName contextKey ctx
    let declared := contextPredStr.toName
    unless entry.contextDecl == declared do
      throwError "backend evidence: {ctx}: semantic anchor mismatch — resolved context \
        '{entry.id.name}' has contextDecl '{entry.contextDecl}', but the record \
        declares '{declared}'"
    pure { shell := p,
           data := .contextRealization theory contextKey entry.id entry.contextDecl
             direction realizationStatus,
           roots := [entry.contextDecl] }
  | "statementAdapter" => do
    let sentence ← getStr j "sentence" ctx
    let capabilityStr ← getStr j "capability" ctx
    let variantKey ← getStr j "variantKey" ctx
    let adapterStatus ← getStr j "adapterStatus" ctx
    unless adapterStatus == "unconditional" do
      throwError "backend evidence: {ctx}: unknown adapterStatus '{adapterStatus}' \
        (only 'unconditional' exists)"
    let entry ← resolveVariant cat nsName variantKey ctx
    let declared := capabilityStr.toName
    let some iface := entry.interface?
      | throwError "backend evidence: {ctx}: resolved variant '{entry.id.name}' is not \
          capability-owning (no registered interface), so it cannot anchor a statement \
          adapter"
    unless iface == declared do
      throwError "backend evidence: {ctx}: semantic anchor mismatch — resolved variant \
        '{entry.id.name}' has interface '{iface}', but the record declares capability \
        '{declared}'"
    pure { shell := p,
           data := .statementAdapter sentence iface variantKey entry.id adapterStatus,
           roots := [iface] }
  | "calculusIdentity" => do
    let calculusId ← getStr j "calculusId" ctx
    let derivability ← getStr j "derivability" ctx
    let soundness ← getStr j "soundness" ctx
    let standardComparison ← getStr j "standardComparison" ctx
    unless standardComparison == "pending" do
      throwError "backend evidence: {ctx}: unknown standardComparison \
        '{standardComparison}' (only 'pending' exists until a pinned standard calculus \
        is compared)"
    pure { shell := p,
           data := .calculusIdentity calculusId derivability soundness
             standardComparison,
           roots := [] }
  | "calculusNonderivability" => do
    let calculusRecord ← getStr j "calculusRecord" ctx
    let sentenceAdapter ← getStr j "sentenceAdapter" ctx
    let theory ← getStr j "theory" ctx
    let sentence ← getStr j "sentence" ctx
    -- calculusId is filled in phase 3 from the referenced record
    pure { shell := p,
           data := .calculusNonderivability calculusRecord sentenceAdapter "" theory
             sentence,
           roots := [] }
  | "semanticCountermodel" => do
    let realizationRef ← getStr j "contextRealization" ctx
    let adapterRef ← getStr j "sentenceAdapter" ctx
    let theory ← getStr j "theory" ctx
    let sentence ← getStr j "sentence" ctx
    let scope ← getStr j "scope" ctx
    unless scope == "allModels" do
      throwError "backend evidence: {ctx}: unknown scope '{scope}' (only 'allModels' \
        exists for semantic countermodels)"
    let modelClass ← getStr j "modelClass" ctx
    unless modelClass == "foundationStruc2General" do
      throwError "backend evidence: {ctx}: unknown modelClass '{modelClass}' (only \
        'foundationStruc2General' exists)"
    let witnessProvenance ← getStr j "witnessProvenance" ctx
    unless witnessProvenance == "omegaStructure" do
      throwError "backend evidence: {ctx}: unknown witnessProvenance \
        '{witnessProvenance}' (only 'omegaStructure' exists — the witness is \
        provenance, not the scope)"
    let witnessBase ← getStr j "witnessBase" ctx
    -- references are linked and identity-checked in phase 3
    pure { shell := p,
           data := .semanticCountermodel realizationRef adapterRef theory sentence
             scope modelClass witnessProvenance witnessBase,
           roots := [] }
  | k => throwError "backend evidence: {ctx}: unknown kind '{k}'"

end BackendEvidence

open BackendEvidence in
/-- `rm_ingest_bridge_evidence "path.json" artifactRevision := "<40-hex>"`: ingest a
versioned backend-evidence file. `artifactRevision` is the backend commit whose tree
contains the vendored artifact byte-for-byte — necessarily distinct from the artifact's
embedded export/check revision, which by self-reference cannot contain the artifact;
both are stored, exported, and rendered. Fail-closed throughout; see the module
docstring for the hard-failure/downgrade boundary. -/
elab "rm_ingest_bridge_evidence " path:str " artifactRevision" " := " artRev:str :
    command => do
  let cat ← requireCleanCatalog
  let content ← try liftM (IO.FS.readFile ⟨path.getString⟩)
    catch e => throwErrorAt path
      "backend evidence: cannot read '{path.getString}': {e.toMessageData}"
  let json ← match Json.parse content with
    | .error e => throwErrorAt path
        "backend evidence: '{path.getString}' is not valid JSON: {e}"
    | .ok j => pure j
  -- envelope
  let schema ← getStr json "schema" "evidence file"
  unless schema == backendEvidenceSchemaV2 do
    throwErrorAt path "backend evidence: unknown schema version '{schema}' (this \
      reader accepts '{backendEvidenceSchemaV2}'); schema changes are versioned, never \
      silently reinterpreted"
  let fpSchema ← getStr json "fingerprintSchema" "evidence file"
  unless fpSchema == fingerprintSchemaV1 do
    throwErrorAt path "backend evidence: unknown fingerprint schema '{fpSchema}' (this \
      reader accepts '{fingerprintSchemaV1}')"
  let source ← getObj json "source" "evidence file"
  let repository ← getStr source "repository" "evidence source"
  if repository.isEmpty then
    throwErrorAt path "backend evidence: source repository must be nonempty"
  let revision ← requireRevision (← getStr source "revision" "evidence source")
    "source revision"
  let artifactRevision ← requireRevision artRev.getString "artifact revision"
  let toolchain ← getStr source "toolchain" "evidence source"
  let deps ← getObj source "dependencies" "evidence source"
  let rmRevision ← requireRevision (← getStr deps "reverse-mathlib" "dependencies")
    "reverse-mathlib dependency revision"
  let foundationRevision ← requireRevision (← getStr deps "Foundation" "dependencies")
    "Foundation dependency revision"
  let mlRevision ← requireRevision (← getStr deps "mathlib" "dependencies")
    "mathlib dependency revision"
  let nsStr ← getStr json "namespace" "evidence file"
  let nsName := nsStr.toName
  unless cat.namespaces.any (·.id.name == nsName) do
    throwErrorAt path "backend evidence: namespace '{nsStr}' is not registered \
      (rm_namespace first; namespaces are extensible by registration)"
  -- downgrade reasons: toolchain coordinates and checking completeness
  let mut downgradeReasons : Array String := #[]
  let ownToolchain := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  if toolchain ≠ ownToolchain then
    downgradeReasons := downgradeReasons.push
      s!"toolchain mismatch (backend {toolchain}, this workspace {ownToolchain}) — the \
        fingerprint closure excludes non-local bodies, so backendChecked is unavailable \
        across a toolchain gap"
  let ownManifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let ownMathlibRev? : Option String := do
    let pkgs ← (ownManifest.getObjValAs? (Array Json) "packages").toOption
    let m ← pkgs.find? fun p => (p.getObjValAs? String "name").toOption == some "mathlib"
    (m.getObjValAs? String "rev").toOption
  match ownMathlibRev? with
  | some ownRev =>
    if mlRevision ≠ ownRev then
      downgradeReasons := downgradeReasons.push
        s!"mathlib revision mismatch (backend {mlRevision}, this workspace {ownRev})"
  | none =>
    downgradeReasons := downgradeReasons.push
      "cannot determine this workspace's mathlib revision"
  let checking := parseChecking json
  downgradeReasons := downgradeReasons ++ checking.reasons
  -- phase 1: parse every record before resolving anything; duplicate ids are hard
  let recordsJson ← getArr json "records" "evidence file"
  let existing := (backendEvidenceExt.getState (← getEnv)).map (·.id)
  let mut shells : Array ParsedRecord := #[]
  let mut seen : Std.HashSet String := {}
  for r in recordsJson do
    let shell ← parseRecordShell r
    if seen.contains shell.id || existing.contains shell.id then
      throwErrorAt path "backend evidence: duplicate record id '{shell.id}'"
    seen := seen.insert shell.id
    shells := shells.push shell
  -- phase 2: kind fields, crosswalks, semantic anchors
  let mut resolved : Array ResolvedRecord := #[]
  for shell in shells do
    resolved := resolved.push (← resolveRecord cat nsName shell)
  -- phase 3: typed record references, order-independent
  let mut linked : Array ResolvedRecord := #[]
  for r in resolved do
    match r.data with
    | .calculusNonderivability calcRef adapterRef _ theory sentence => do
      let ctx := s!"record '{r.shell.id}'"
      let some calcRec := resolved.find? (·.shell.id == calcRef)
        | throwErrorAt path "backend evidence: {ctx}: calculusRecord '{calcRef}' does \
            not name a record in this file"
      let calculusId ← match calcRec.data with
        | .calculusIdentity cid _ _ _ => pure cid
        | d => throwErrorAt path "backend evidence: {ctx}: calculusRecord '{calcRef}' \
            has kind '{d.kindTag}', not calculusIdentity"
      let some adapter := resolved.find? (·.shell.id == adapterRef)
        | throwErrorAt path "backend evidence: {ctx}: sentenceAdapter '{adapterRef}' \
            does not name a record in this file"
      match adapter.data with
        | .statementAdapter s _ _ _ _ =>
          unless s == sentence do
            throwErrorAt path "backend evidence: {ctx}: sentence '{sentence}' \
              disagrees with referenced adapter's sentence '{s}'"
        | d => throwErrorAt path "backend evidence: {ctx}: sentenceAdapter \
            '{adapterRef}' has kind '{d.kindTag}', not statementAdapter"
      linked := linked.push { r with
        data := .calculusNonderivability calcRef adapterRef calculusId theory sentence,
        roots := adapter.roots }
    | .semanticCountermodel realizationRef adapterRef theory sentence scope
        modelClass wp wb => do
      let ctx := s!"record '{r.shell.id}'"
      let some realization := resolved.find? (·.shell.id == realizationRef)
        | throwErrorAt path "backend evidence: {ctx}: contextRealization \
            '{realizationRef}' does not name a record in this file"
      match realization.data with
        | .contextRealization t _ _ _ _ _ =>
          unless t == theory do
            throwErrorAt path "backend evidence: {ctx}: theory '{theory}' disagrees \
              with referenced realization's theory '{t}' — the reference is an \
              identity check only"
        | d => throwErrorAt path "backend evidence: {ctx}: contextRealization \
            '{realizationRef}' has kind '{d.kindTag}', not contextRealization"
      let some adapter := resolved.find? (·.shell.id == adapterRef)
        | throwErrorAt path "backend evidence: {ctx}: sentenceAdapter '{adapterRef}' \
            does not name a record in this file"
      match adapter.data with
        | .statementAdapter sSent _ _ _ _ =>
          unless sSent == sentence do
            throwErrorAt path "backend evidence: {ctx}: sentence '{sentence}' \
              disagrees with referenced adapter's sentence '{sSent}' — the reference \
              is an identity check only, never an all-model adapter to any local \
              capability"
        | d => throwErrorAt path "backend evidence: {ctx}: sentenceAdapter \
            '{adapterRef}' has kind '{d.kindTag}', not statementAdapter"
      linked := linked.push { r with
        data := .semanticCountermodel realizationRef adapterRef theory sentence scope
          modelClass wp wb,
        roots := [] }
    | _ => linked := linked.push r
  -- phase 4: fingerprints recomputed from the resolved local roots
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let owned : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => (`ReverseMathlib).isPrefixOf (moduleNames.getD idx.toNat .anonymous)
    | none => (`ReverseMathlib).isPrefixOf n
  let roots := linked.foldl (fun acc r => acc ++ r.roots) []
  let localManifest ← match InterfaceExpr.manifest env owned roots with
    | .ok m => pure m
    | .error e => throwErrorAt path "backend evidence: fingerprint recomputation \
        failed: {e}"
  let fpJson ← getArr json "fingerprints" "evidence file"
  let mut fileManifest : Array (Name × String) := #[]
  for f in fpJson do
    let n ← getStr f "name" "fingerprint entry"
    let p ← getStr f "canonicalInterface" s!"fingerprint '{n}'"
    fileManifest := fileManifest.push (n.toName, p)
  let fileSorted := fileManifest.qsort fun a b => Name.lt a.1 b.1
  let localNames := localManifest.map (·.1)
  let fileNames := fileSorted.toList.map (·.1)
  if localNames ≠ fileNames then
    let missing := localNames.filter (!fileNames.contains ·)
    let extra := fileNames.filter (!localNames.contains ·)
    throwErrorAt path "backend evidence: fingerprint coverage mismatch — the covered \
      declaration sets differ ({localNames.length} required locally, \
      {fileNames.length} in file; {missing.length} missing\
      {match missing.head? with | some n => s!", first '{n}'" | none => ""}; \
      {extra.length} extra\
      {match extra.head? with | some n => s!", first '{n}'" | none => ""}); an under- \
      or over-covered manifest is rejected whole"
  for ((n, localP), (_, fileP)) in localManifest.zip fileSorted.toList do
    if localP ≠ fileP then
      throwErrorAt path "backend evidence: fingerprint mismatch at '{n}' — the \
        backend's checked interface differs from this workspace's declaration; \
        revision drift is acceptable only when the semantic interface is unchanged"
  -- final status and storage: per-record coordinate completeness (empty strings count
  -- as missing — malformed trust coordinates must never become backendChecked)
  for r in linked do
    let theoremName? := nonempty? r.shell.theoremName?
    let mut recordReasons := downgradeReasons
    if theoremName?.isNone &&
        ["contextRealization", "statementAdapter",
          "calculusNonderivability", "semanticCountermodel"].contains r.shell.kind then
      recordReasons := recordReasons.push "missing theorem"
    if r.shell.exportName.isEmpty then
      recordReasons := recordReasons.push "empty export name"
    if let .calculusIdentity _ derivability soundness _ := r.data then
      if soundness.isEmpty then
        recordReasons := recordReasons.push "empty soundness name"
      if derivability.isEmpty then
        recordReasons := recordReasons.push "empty derivability name"
    let (status, reason?) :=
      if r.shell.claimedStatus == "reported" then
        (BackendStatus.reported, some "reported at source")
      else if recordReasons.isEmpty then
        (BackendStatus.backendChecked, none)
      else
        (BackendStatus.reported,
          some (String.intercalate "; " recordReasons.toList))
    modifyEnv fun env => backendEvidenceExt.addEntry env
      { id := r.shell.id, ns := ⟨nsName⟩, repository, revision, artifactRevision,
        artifactPath := path.getString, rmRevision, foundationRevision,
        mathlibRevision := mlRevision, toolchain, mechanism? := checking.mechanism?,
        audit? := checking.audit?, allowedAxioms := checking.allowedAxioms,
        exportName := r.shell.exportName, theoremName?,
        status, downgraded? := reason?, data := r.data }
    -- a fully validated, undowngraded countermodel contributes a checked scoped
    -- result (Registry-owned extension; dedup by semantic key at count time);
    -- any downgrade contributes nothing — the all-model column falls back to 0
    if status == .backendChecked then
      if let .semanticCountermodel _ _ theory sentence _ modelClass _ _ := r.data then
        modifyEnv fun env => scopedResultExt.addEntry env
          { scope := .allModels, verification := .backendChecked,
            kind := "semanticCountermodel", modelClass, theory, sentence,
            sourceId := r.shell.id }

/-- Scope-safe rendering of one record — generated from the typed fields, so the
calculus and comparison qualifiers cannot be dropped without changing the data. -/
def BackendEvidenceEntry.render (e : BackendEvidenceEntry) : String :=
  match e.data with
  | .contextRealization theory _ context _ _ _ =>
    s!"context realization [forward, realizationOnly]: every '{context.name}' context \
      realizes backend theory {theory} — one-way evidence, never an unrestricted \
      semantic claim"
  | .statementAdapter sentence capability _ variant _ =>
    s!"statement adapter [unconditional]: backend sentence {sentence} ↔ \
      '{variant.name}' (interface {capability}) at every second-order part"
  | .calculusIdentity calculusId _ soundness comparison =>
    s!"calculus identity: backend-local calculus '{calculusId}' with soundness \
      {soundness}; standard-calculus comparison {comparison}"
  | .calculusNonderivability _ _ calculusId theory sentence =>
    s!"nonderivability [calculus-relative]: {theory} ⊬ {sentence} in '{calculusId}', \
      with standard-calculus comparison pending — never an unqualified turnstile claim"
  | .semanticCountermodel _ _ theory sentence _ _ _ witnessBase =>
    s!"semantic countermodel [allModels, foundationStruc2General]: {theory} ⊭ \
      {sentence} over all general (Henkin-style) second-order L₂ structures — the \
      standard model class for subsystems of Z₂; witnessed by the ω-structure over \
      {witnessBase} (an ω-countermodel is in particular an L₂ countermodel; witness \
      provenance, not scope). Never an unqualified conventional-RCA₀ claim: the \
      theory-presentation comparison stays pending"

/-- `#rm_backend_evidence`: display the backend-evidence records, sorted by id.
External backend evidence only — never axioms, never certified counts, no port, no
closure edge, no concept-strength graph edge. -/
elab "#rm_backend_evidence" : command => do
  let _ ← requireCleanCatalog
  let entries := (backendEvidenceExt.getState (← getEnv)).qsort fun a b => a.id < b.id
  let mut lines := #[s!"backend evidence ({entries.size}) — external backend evidence: \
    never axioms, no certified counts, no ports, no closure edges, no graph edges:"]
  for e in entries do
    lines := lines.push s!"  {e.ns.name}:\"{e.id}\" [{e.data.kindTag}] — {e.status.tag}"
    lines := lines.push s!"    {e.render}"
    lines := lines.push s!"    source: {e.repository} — export/check @ {e.revision}, \
      artifact @ {e.artifactRevision} ({e.artifactPath})"
    lines := lines.push s!"    dependencies: reverse-mathlib {e.rmRevision}; \
      Foundation {e.foundationRevision}; mathlib {e.mathlibRevision}; toolchain \
      {e.toolchain}"
    let mech := e.mechanism?.getD "(none)"
    let audit := e.audit?.getD "(none)"
    lines := lines.push s!"    checking: mechanism {mech}; audit {audit}; allowed \
      axioms {e.allowedAxioms.toList}"
    match e.theoremName? with
    | some t => lines := lines.push s!"    theorem: {t}; export: {e.exportName}"
    | none => lines := lines.push s!"    export: {e.exportName}"
    if let some reason := e.downgraded? then
      lines := lines.push s!"    downgraded: {reason}"
  logInfo ("\n".intercalate lines.toList)

end ReverseMathlib.Meta
