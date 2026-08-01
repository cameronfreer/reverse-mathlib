/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Concepts

/-!
# Corpus audits: pinned external classification claims (issue #7)

Typed records of what external corpora — databases, books, theses — *classify*, kept
strictly apart from this catalog's own facts and evidence. The discipline:

* **Every source is pinned**: a database revision, an edition, a publication year — a
  corpus claim cites a registered pinned source plus a locator (section, symbol, line).
* **Source wording is preserved separately** from the normalized claim, with its kind
  declared: `verbatim`, `paraphrase`, or `absent` — a paraphrase can never masquerade as
  a quotation.
* **Claims are concept-level**: a corpus claim names registered *concepts* and carries a
  prose normalization. It is never promoted to an exact statement variant, registers no
  fact, and links no evidence — literature evidence is `reported`, full stop.
* **Presentation families are first-class**: each claim is tagged with the registered
  formulation family its source actually treats, so a one-sided enumerated family, a
  two-sided marriage system, and a perfect-matching formulation can never be conflated.
* **Missing bridges are explicit**: a `rm_presentation_bridge` record states exactly
  which theorem would have to be proved before a corpus classification transfers to one
  of this catalog's exact variants or represented problems; until then its status is
  `missing` and every display says so.

Fail-closed throughout: unregistered namespaces, sources, concepts, families, or bridge
targets are hard errors, as are duplicate ids and wording/kind mismatches.
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- A pinned corpus source: a registered namespace plus the exact pin (database revision,
edition, year) the audit consulted. -/
structure CorpusSourceEntry where
  /-- The registered namespace this source pins. -/
  ns : ExternalNamespaceId
  /-- The pin: a database revision, an edition, a publication identifier. -/
  pin : String
  /-- What was consulted, bibliographically. -/
  description : String
  deriving Inhabited, Repr, BEq

/-- A registered presentation family (one-sided enumerated, two-sided marriage,
perfect matching, …) — extensible by registration, never a closed enum. -/
structure PresentationFamilyEntry where
  /-- The identifying name. -/
  id : Name
  /-- What formulations belong to this family. -/
  description : String
  deriving Inhabited, Repr, BEq

/-- How a claim's recorded wording relates to the source. -/
inductive WordingKind where
  /-- A quotation. -/
  | verbatim
  /-- A paraphrase, marked as such. -/
  | paraphrase
  /-- No wording captured; the locator alone points at the source. -/
  | absent
  deriving Inhabited, Repr, BEq

/-- Stable tag for a wording kind. -/
def WordingKind.tag : WordingKind → String
  | .verbatim => "verbatim"
  | .paraphrase => "paraphrase"
  | .absent => "absent"

/-- A corpus claim: what a pinned source classifies, at concept level, in the source's own
presentation family. Always `reported`; never a fact, never evidence. -/
structure CorpusClaimEntry where
  /-- The record id. -/
  id : Name
  /-- The pinned source's namespace. -/
  source : ExternalNamespaceId
  /-- The locator inside the source (section, symbol, line). -/
  locator : String
  /-- How the recorded wording relates to the source. -/
  wordingKind : WordingKind
  /-- The preserved source wording (empty exactly when `wordingKind` is `absent`). -/
  wording : String
  /-- The registered concepts the claim is about — concept-level, never variants. -/
  concepts : Array ConceptId
  /-- The registered presentation family the source's formulation belongs to. -/
  family : Name
  /-- The normalized concept-level claim, as prose. -/
  claim : String
  deriving Inhabited, Repr, BEq

/-- A presentation bridge requirement: what would have to be proved before a corpus
classification transfers to an exact catalog object. -/
structure PresentationBridgeEntry where
  /-- The record id. -/
  id : Name
  /-- The source presentation family. -/
  fromFamily : Name
  /-- The exact catalog object a transfer would target. -/
  target : CatalogObjectRef
  /-- Exactly which theorem is required. -/
  requirement : String
  deriving Inhabited, Repr, BEq

initialize corpusSourceExt :
    SimplePersistentEnvExtension CorpusSourceEntry (Array CorpusSourceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize presentationFamilyExt :
    SimplePersistentEnvExtension PresentationFamilyEntry (Array PresentationFamilyEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize corpusClaimExt :
    SimplePersistentEnvExtension CorpusClaimEntry (Array CorpusClaimEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize presentationBridgeExt :
    SimplePersistentEnvExtension PresentationBridgeEntry (Array PresentationBridgeEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

/-- `rm_corpus_source ns "pin" "description"`: pin a registered namespace as an audited
corpus source. -/
elab "rm_corpus_source " ns:ident pin:str desc:str : command => do
  let env ← getEnv
  let cat := ConceptCatalog.ofEnv env
  unless cat.namespaces.any (·.id.name == ns.getId) do
    throwErrorAt ns "corpus: namespace '{ns.getId}' is not registered (rm_namespace first)"
  if (corpusSourceExt.getState env).any (·.ns.name == ns.getId) then
    throwErrorAt ns "corpus: source '{ns.getId}' is already pinned"
  if pin.getString.isEmpty then
    throwErrorAt pin "corpus: a corpus source requires a nonempty pin (revision, edition, \
      or publication identifier)"
  modifyEnv fun env => corpusSourceExt.addEntry env
    ⟨⟨ns.getId⟩, pin.getString, desc.getString⟩

/-- `rm_presentation_family id "description"`: register a presentation family. -/
elab "rm_presentation_family " id:ident desc:str : command => do
  let env ← getEnv
  if (presentationFamilyExt.getState env).any (·.id == id.getId) then
    throwErrorAt id "corpus: duplicate presentation family '{id.getId}'"
  modifyEnv fun env => presentationFamilyExt.addEntry env ⟨id.getId, desc.getString⟩

/-- `rm_corpus_claim id where source := ns "locator" family := fam
concepts := [c, …] wording := (verbatim|paraphrase) "…" | absent claim := "…"`:
record what a pinned source classifies, at concept level. -/
syntax (name := rmCorpusClaimCmd) "rm_corpus_claim " ident " where "
  &"source" " := " ident str
  &"family" " := " ident
  &"concepts" " := " "[" ident,* "]"
  &"wording" " := " ident (str)?
  &"claim" " := " str : command

@[command_elab rmCorpusClaimCmd]
def elabRmCorpusClaim : CommandElab := fun stx => do
  let env ← getEnv
  let cat := ConceptCatalog.ofEnv env
  let id := stx[1]
  let ns := stx[5]
  let loc := stx[6]
  let fam := stx[9]
  let cs := stx[13].getSepArgs
  let wk := stx[17]
  let w? := if stx[18].getNumArgs == 0 then none else some stx[18][0]
  let cl := stx[21]
  if (corpusClaimExt.getState env).any (·.id == id.getId) then
    throwErrorAt id "corpus: duplicate corpus claim '{id.getId}'"
  unless (corpusSourceExt.getState env).any (·.ns.name == ns.getId) do
    throwErrorAt ns "corpus: source '{ns.getId}' is not a pinned corpus source \
      (rm_corpus_source first — audits cite pinned corpora only)"
  unless (presentationFamilyExt.getState env).any (·.id == fam.getId) do
    throwErrorAt fam "corpus: unknown presentation family '{fam.getId}'"
  let mut concepts : Array ConceptId := #[]
  for c in cs do
    unless cat.concepts.any (·.id.name == c.getId) do
      throwErrorAt c "corpus: unknown concept '{c.getId}' — corpus claims are \
        concept-level and never promote to exact variants"
    concepts := concepts.push ⟨c.getId⟩
  let (kind, wording) ← match wk.getId, w? with
    | `verbatim, some ws =>
      if ws.isStrLit?.getD "" |>.isEmpty then
        throwErrorAt ws "corpus: verbatim wording must be nonempty"
      pure (WordingKind.verbatim, (ws.isStrLit?.getD ""))
    | `paraphrase, some ws =>
      if ws.isStrLit?.getD "" |>.isEmpty then
        throwErrorAt ws "corpus: paraphrase wording must be nonempty"
      pure (WordingKind.paraphrase, (ws.isStrLit?.getD ""))
    | `absent, none => pure (WordingKind.absent, "")
    | `absent, some ws => throwErrorAt ws "corpus: wording kind 'absent' carries no text"
    | other, _ => throwErrorAt wk "corpus: unknown wording kind '{other}' (expected \
        verbatim | paraphrase | absent; verbatim and paraphrase take a string)"
  modifyEnv fun env => corpusClaimExt.addEntry env
    ⟨id.getId, ⟨ns.getId⟩, loc.isStrLit?.getD "", kind, wording, concepts, fam.getId,
      cl.isStrLit?.getD ""⟩

/-- `rm_presentation_bridge id where family := fam to := (uniformProblem|statement) x
requires := "…"`: record, explicitly, the theorem that is missing before a corpus
classification in family `fam` transfers to the exact target. -/
syntax (name := rmBridgeCmd) "rm_presentation_bridge " ident " where "
  &"family" " := " ident
  &"to" " := " ident ident
  &"requires" " := " str : command

@[command_elab rmBridgeCmd]
def elabRmBridge : CommandElab := fun stx => do
  let env ← getEnv
  let cat := ConceptCatalog.ofEnv env
  let id := stx[1]
  let fam := stx[5]
  let kind := stx[8]
  let tgt := stx[9]
  let req := stx[12]
  if (presentationBridgeExt.getState env).any (·.id == id.getId) then
    throwErrorAt id "corpus: duplicate presentation bridge '{id.getId}'"
  unless (presentationFamilyExt.getState env).any (·.id == fam.getId) do
    throwErrorAt fam "corpus: unknown presentation family '{fam.getId}'"
  let target ← match kind.getId with
    | `uniformProblem => do
      unless cat.problems.any (·.id.name == tgt.getId) do
        throwErrorAt tgt "corpus: unknown uniform problem '{tgt.getId}'"
      pure (CatalogObjectRef.uniformProblem ⟨tgt.getId⟩)
    | `statement => do
      unless cat.variants.any (·.id.name == tgt.getId) do
        throwErrorAt tgt "corpus: unknown statement variant '{tgt.getId}'"
      pure (CatalogObjectRef.statement ⟨tgt.getId⟩)
    | other => throwErrorAt kind "corpus: bridge targets are exact catalog objects \
        (uniformProblem | statement), got '{other}'"
  if req.isStrLit?.getD "" |>.isEmpty then
    throwErrorAt req "corpus: a bridge record must state its required theorem"
  modifyEnv fun env => presentationBridgeExt.addEntry env
    ⟨id.getId, fam.getId, target, req.isStrLit?.getD ""⟩

/-- `#rm_corpus`: the corpus-audit view — pinned sources, presentation families, claims
(wording kept apart from the normalization), and the explicitly missing bridges. -/
elab "#rm_corpus" : command => do
  let env ← getEnv
  let sources := (corpusSourceExt.getState env).qsort fun a b =>
    a.ns.name.toString < b.ns.name.toString
  let families := (presentationFamilyExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  let claims := (corpusClaimExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  let bridges := (presentationBridgeExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  let mut lines := #[s!"corpus sources ({sources.size}):"]
  for s in sources do
    lines := lines.push s!"  {s.ns.name} @ {s.pin} — {s.description}"
  lines := lines.push s!"presentation families ({families.size}):"
  for f in families do
    lines := lines.push s!"  {f.id} — {f.description}"
  lines := lines.push s!"corpus claims ({claims.size}) — all reported; concept-level, \
    never facts, never evidence:"
  for c in claims do
    let subjects := ", ".intercalate (c.concepts.toList.map fun i => toString i.name)
    lines := lines.push s!"  {c.id} [{c.source.name}:\"{c.locator}\" | {c.family}] \
      concepts: {subjects}"
    match c.wordingKind with
    | .absent => lines := lines.push s!"    wording: (not captured; locator only)"
    | k => lines := lines.push s!"    wording ({k.tag}): {c.wording}"
    lines := lines.push s!"    normalized: {c.claim}"
  lines := lines.push s!"presentation bridges ({bridges.size}) — every one MISSING until \
    a named theorem lands:"
  for b in bridges do
    lines := lines.push s!"  {b.id}: {b.fromFamily} → [{b.target.kindTag}] \
      {b.target.name} — MISSING"
    lines := lines.push s!"    requires: {b.requirement}"
  logInfo ("\n".intercalate lines.toList)

end ReverseMathlib.Meta
