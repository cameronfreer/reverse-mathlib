/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Meta.Corpus
import ReverseMathlib.Meta.Interchange
import ReverseMathlib.Meta.BackendEvidence

/-!
# Deterministic catalog export

`#rm_export_catalog "path"` writes the canonical direct-catalog JSON
(`reverse-mathlib.catalog/v5`) extracted from the **elaborated environment's persistent
extension state** — never by parsing Lean source or scraping human-readable command output.
The persistent extensions have already resolved names and validated certificates; they are the
right extraction point.

Schema history, versioned per the "schema changes are versioned" discipline: `v0` was the
transitional pre-conceptual export; `v1` added the corpus family; `v2` added the
`importedReductions` family with **both sides of every crosswalk** — the external keys as
ingested and the resolved local ids — so the canonical artifact can be audited
independently of the Lean environment; `v3` admits certified `nonImplication` facts
(countermodel-witnessed separations) among the fact kinds a consumer must understand —
they are never edges of any implication closure and never turnstile claims; `v4` adds the
`backendEvidence` family (external checked backend records with both sides of every
crosswalk, their typed record references, and their trust statuses — never certified
facts, never graph edges) and admits `semanticContext` among external-reference target
kinds.

Canonical-file properties:

* IDs are canonical strings (declaration and registry names), never generated numerics;
* **set-like arrays are canonically sorted; order-bearing arrays preserve declared order** —
  in particular each port's `evidence` array keeps registration order, because `evidenceIdx`
  refers to it. Every ordering rule is explicit: concepts, layers, variants, problems,
  namespaces, ports, base theories, formula classes, reducibility notions, and facts by id,
  refs by (namespace, key, target), ambient nodes
  by name, ambient edges by (source, target, port, evidenceIdx), evidence in declared order;
* typed facts export **fail-closed**: a fact's `evidence` array contains exactly its
  registered certifications (`revmath_certify_fact`, #24) — context, certificate, note;
  uncertified facts export `"evidence": []` and are never rendered as supported;
* machine-readable fields carry **stable tags** (`relativeProof`, `kernelChecked`, `lean`, …),
  never rendered prose; human labels live in separate `display` objects, so editing display
  wording is never a schema migration;
* **no timestamp** — the canonical file depends only on the environment and pin;
* evidence is exported in full, never collapsed to a maturity score;
* source locations are module names (declaration ranges are *not* promised in v0), never
  absolute build-machine paths;
* build provenance records the Lean version and the pinned mathlib revision (or the explicit
  string `"unavailable"`, which CI treats as a failure).

The `ambientGraph` section is the honest **ambient-factorization view**: nodes are the Lean
statements, edges are kernel-checked `RelativeCertificate`s in unrestricted Lean. Endpoints are
derived **direction-aware** — `upper` is principle interface → port statement, `lower` is port
statement → principle interface, `exact` contributes both — never by treating the assumed
principle as the source unconditionally. Nothing here is an RM implication: every edge carries
`"scope": "ambientFactorization"`, which the registry classifies as *not* an RM bound.
-/

namespace ReverseMathlib.Meta

open Lean

/-- Build provenance for machine-readable artifacts: a catalog file is meaningless without the
toolchain and library pin it was extracted against. -/
structure BuildProvenance where
  /-- The Lean version string. -/
  leanVersion : String
  /-- The pinned mathlib revision, or `"unavailable"` (explicit, never omitted). -/
  mathlibRevision : String

/-- Read provenance (mathlib revision best-effort from `lake-manifest.json`, rendered
`"unavailable"` when absent — fail closed, never silent). -/
def BuildProvenance.read : IO BuildProvenance := do
  let rev? ← readMathlibRev
  return { leanVersion := Lean.versionString, mathlibRevision := rev?.getD "unavailable" }

/-- One edge of the ambient-factorization graph: a kernel-checked relative certificate,
with direction-aware endpoints. -/
structure AmbientEdge where
  /-- Source statement (a Lean `Prop` declaration name). -/
  source : Name
  /-- Target statement. -/
  target : Name
  /-- The registry port the evidence belongs to. -/
  port : Name
  /-- Index of the evidence record within the port. -/
  evidenceIdx : Nat
  /-- The bound direction of the originating evidence. -/
  direction : BoundDirection
  /-- The typed certificate. -/
  certificate : Name
  deriving Inhabited, Repr, BEq

/-- The direct catalog snapshot: exactly what is registered, plus the derived ambient edges. -/
structure CatalogSnapshot where
  /-- Registered ports, sorted by id. -/
  ports : Array PortEntry
  /-- Ambient-factorization edges, sorted by (source, target, port, evidenceIdx). -/
  ambientEdges : Array AmbientEdge
  /-- The conceptual catalog (concepts, namespaces, typed external references). The exporter
  refuses to run on a conflicted state. -/
  conceptCatalog : ConceptCatalog
  /-- Fact certifications (#24), sorted by (fact, certificate). -/
  factEvidence : Array FactEvidenceEntry

/-- Derive the ambient-factorization edges of one port. Direction-aware: `upper` maps
the assumed variant's interface → the target's interface, `lower` maps target → assumed,
`exact` contributes both directions. Only kernel-checked `relativeProof` evidence with
resolvable endpoints yields edges. -/
def ambientEdgesOf (cat : ConceptCatalog) (p : PortEntry) :
    Array AmbientEdge := Id.run do
  let mut edges := #[]
  let some portDecl := p.portDecl? | return #[]
  let mut i := 0
  for e in p.evidence do
    if e.kind == .relativeProof && e.verification == .kernelChecked then
      if let (some cert, some assumes) := (e.thm?, e.assumes?) then
        if let some ventry := cat.findVariant? assumes.name then
          if let some interface := ventry.interface? then
            let mk (src tgt : Name) : AmbientEdge :=
              { source := src, target := tgt, port := p.id, evidenceIdx := i,
                direction := e.direction, certificate := cert }
            match e.direction with
            | .upper => edges := edges.push (mk interface portDecl)
            | .lower => edges := edges.push (mk portDecl interface)
            | .exact =>
              edges := edges.push (mk interface portDecl)
              edges := edges.push (mk portDecl interface)
    i := i + 1
  return edges

/-- Extract the snapshot from an elaborated environment. Deterministic: set-like arrays
sorted, order-bearing (evidence) arrays preserved. -/
def CatalogSnapshot.ofEnv (env : Environment) : CatalogSnapshot :=
  let cat := ConceptCatalog.ofEnv env
  let ports := (portExt.getState env).qsort fun a b => toString a.id < toString b.id
  let factEvidence := (factEvidenceExt.getState env).qsort fun a b =>
    toString a.fact.name < toString b.fact.name ||
      (a.fact == b.fact && toString a.thm < toString b.thm)
  let edges := (ports.flatMap (ambientEdgesOf cat)).qsort fun a b =>
    Name.lt a.source b.source ||
      (a.source == b.source && (Name.lt a.target b.target ||
        (a.target == b.target && (Name.lt a.port b.port ||
          (a.port == b.port && a.evidenceIdx < b.evidenceIdx)))))
  { ports, ambientEdges := edges, conceptCatalog := cat, factEvidence }

/-- Owning module of a declaration, or `null` for current-file declarations. Module names,
never file paths. -/
def moduleJson (env : Environment) (n : Name) : Json :=
  match env.getModuleIdxFor? n with
  | some idx => match env.allImportedModuleNames[idx.toNat]? with
    | some m => Json.str (toString m)
    | none => Json.null
  | none => Json.null

private def nameJson : Name → Json := fun n => Json.str (toString n)

private def optNameJson : Option Name → Json
  | some n => nameJson n
  | none => Json.null

private def optStrJson : Option String → Json
  | some s => Json.str s
  | none => Json.null

/-! Stable machine tags. These are the schema; the `render` functions are display only. -/

/-- Stable tag for an evidence kind. -/
def EvidenceKind.tag : EvidenceKind → String
  | .dependencyAudit => "dependencyAudit"
  | .frontierSlice => "frontierSlice"
  | .relativeProof => "relativeProof"
  | .fragmentCheck => "fragmentCheck"
  | .semanticImplication => "semanticImplication"
  | .syntacticDerivation => "syntacticDerivation"

/-- Stable tag for a verification. -/
def Verification.tag : Verification → String
  | .claimed => "claimed"
  | .kernelChecked => "kernelChecked"
  | .backendChecked => "backendChecked"

/-- Stable tag for a proof ambient. -/
def ProofAmbient.tag : ProofAmbient → String
  | .lean => "lean"
  | .checkedFragment _ => "checkedFragment"
  | .modelSemantics => "modelSemantics"
  | .objectTheory => "objectTheory"

/-- Stable tag for a semantic scope, or `null` when absent. -/
def scopeTagJson : Option SemanticScope → Json
  | none => Json.null
  | some .fullStandardModel => Json.str "fullStandardModel"
  | some .omegaModels => Json.str "omegaModels"
  | some .allModels => Json.str "allModels"

/-- Stable tag for a port relation. -/
def PortRelation.tag : PortRelation → String
  | .proofAnalogue => "proofAnalogue"
  | .minedArchitecture => "minedArchitecture"
  | .exactSpecialization => "exactSpecialization"
  | .conceptualAnalogue => "conceptualAnalogue"

/-- Render an evidence record in full — never collapsed to a maturity score. Machine tags in
the main fields; human labels in `display`. -/
def evidenceJson (e : EvidenceRecord) : Json :=
  Json.mkObj
    [("kind", Json.str e.kind.tag),
     ("direction", Json.str e.direction.render),
     ("verification", Json.str e.verification.tag),
     ("ambient", Json.str e.ambient.tag),
     ("semanticScope", scopeTagJson e.scope?),
     ("context", optNameJson (e.context?.map (·.name))),
     ("theory", optNameJson (e.theory?.map (·.name))),
     ("route", optStrJson (e.route?.map (·.tag))),
     ("artifact", optStrJson (e.artifact?.map (·.tag))),
     ("certificate", optNameJson e.thm?),
     ("assumes", (e.assumes?.map fun v => Json.str v.serialized).getD Json.null),
     ("note", Json.str e.note),
     ("display", Json.mkObj
       [("kind", Json.str e.kind.render),
        ("verification", Json.str e.verification.render),
        ("ambient", Json.str e.ambient.render),
        ("scope", Json.str (renderScope e.scope?))])]

/-- The corpus section: pinned external classification claims — a separate top-level
family, never fact-graph edges, never certified counts. A claim's absence finding means
"not found in this pinned corpus snapshot", never a mathematical negation; a `missing`
bridge is an unproved requirement, never evidence that no bridge exists. Claims are
concept-level: their subjects are concepts, deliberately not attached to variants. -/
def corpusJson (env : Environment) : Json :=
  let sources := (corpusSourceExt.getState env).qsort fun a b =>
    a.ns.name.toString < b.ns.name.toString
  let families := (presentationFamilyExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  let claims := (corpusClaimExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  let bridges := (presentationBridgeExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  let audits := (corpusAuditExt.getState env).qsort fun a b =>
    a.id.toString < b.id.toString
  Json.mkObj
    [("comment", Json.str "pinned external classification claims — scoped literature \
        findings, a separate family: never fact-graph edges, never certified counts. \
        Absence findings mean 'not found in this pinned corpus snapshot', never a \
        mathematical negation; a 'missing' bridge is an unproved requirement, never \
        evidence that no bridge exists"),
     ("sources", Json.arr (sources.map fun s => Json.mkObj
       [("namespace", Json.str (toString s.ns.name)),
        ("pin", Json.str s.pin),
        ("description", Json.str s.description)])),
     ("presentationFamilies", Json.arr (families.map fun f => Json.mkObj
       [("id", Json.str (toString f.id)),
        ("description", Json.str f.description)])),
     ("claims", Json.arr (claims.map fun c => Json.mkObj
       [("id", Json.str (toString c.id)),
        ("source", Json.str (toString c.source.name)),
        ("locator", Json.str c.locator),
        ("wordingKind", Json.str c.wordingKind.tag),
        ("wording", if c.wordingKind == .absent then Json.null else Json.str c.wording),
        ("level", Json.str "concept"),
        ("concepts", Json.arr (c.concepts.map fun i =>
          Json.str s!"reverse-mathlib:{i.name}")),
        ("presentationFamily", Json.str (toString c.family)),
        ("normalizedClaim", Json.str c.claim),
        ("status", Json.str "reported")])),
     ("bridges", Json.arr (bridges.map fun b => Json.mkObj
       [("id", Json.str (toString b.id)),
        ("fromFamily", Json.str (toString b.fromFamily)),
        ("target", Json.mkObj
          [("kind", Json.str b.target.kindTag),
           ("id", Json.str s!"reverse-mathlib:{b.target.name}")]),
        ("status", Json.str "missing"),
        ("requirement", Json.str b.requirement)])),
     ("audits", Json.arr (audits.map fun a => Json.mkObj
       [("id", Json.str (toString a.id)),
        ("scope", Json.str a.scope),
        ("outcome", Json.str a.outcome)]))]

/-- Serialize the snapshot with provenance to canonical JSON. -/
def CatalogSnapshot.toJson (snapshot : CatalogSnapshot) (env : Environment)
    (provenance : BuildProvenance) : Json :=
  let portJson (p : PortEntry) : Json :=
    Json.mkObj
      [("id", nameJson p.id),
       ("mathlibDecl", optNameJson p.mathlibDecl?),
       ("mathlibModule", (p.mathlibDecl?.map (moduleJson env)).getD Json.null),
       ("target", Json.str p.target.serialized),
       ("portDecl", optNameJson p.portDecl?),
       ("relation", Json.str p.relation.tag),
       ("literatureNote", optStrJson p.claimedClassical?),
       ("note", Json.str p.note),
       ("display", Json.mkObj [("relation", Json.str p.relation.render)]),
       ("evidence", Json.arr (p.evidence.map evidenceJson))]
  let edgeJson (e : AmbientEdge) : Json :=
    Json.mkObj
      [("source", nameJson e.source),
       ("target", nameJson e.target),
       ("direction", Json.str e.direction.render),
       ("certificate", nameJson e.certificate),
       ("port", nameJson e.port),
       ("evidenceIdx", Json.num e.evidenceIdx),
       ("scope", Json.str "ambientFactorization")]
  let nodes := (snapshot.ambientEdges.flatMap fun e => #[e.source, e.target])
  -- explicitly sorted and deduplicated — never relying on set-iteration order
  let nodes := ((nodes.foldl (init := ({} : NameSet)) fun s n => s.insert n).toArray).qsort
    Name.lt
  let variantOfInterface (n : Name) : Json :=
    match snapshot.conceptCatalog.interfaceOwner[n]? with
    | some v => Json.str v.serialized
    | none => Json.null
  let nodeJson (n : Name) : Json :=
    Json.mkObj
      [("id", nameJson n),
       ("module", moduleJson env n),
       ("statementVariant", variantOfInterface n),
       ("display", Json.mkObj [("label", Json.str (toString (n.componentsRev.headD n)))])]
  let cat := snapshot.conceptCatalog
  let conceptJson (c : ConceptEntry) : Json :=
    Json.mkObj
      [("id", Json.str c.id.serialized),
       ("description", Json.str c.description),
       ("display", Json.mkObj [("label", Json.str c.displayLabel)])]
  let layerJson (l : SemanticLayerEntry) : Json :=
    Json.mkObj
      [("id", Json.str (toString l.id.name)),
       ("interfaceSchema", optNameJson l.interfaceSchema?),
       ("description", Json.str l.description)]
  let vocabJson (id : Name) (description : String) : Json :=
    Json.mkObj
      [("id", Json.str (toString id)),
       ("description", Json.str description)]
  let conjJson (c : VariantConjunction) : Json :=
    Json.arr (c.variants.map fun v => Json.str v.serialized)
  let factContextJson : FactContext → Json
    | .theoryContext b s => Json.mkObj
        [("kind", Json.str "theory"),
         ("base", Json.str (toString b.name)),
         ("scope", Json.str s.tag)]
    | .uniformContext n => Json.mkObj
        [("kind", Json.str "uniform"),
         ("notion", Json.str (toString n.name))]
  let factJson (f : FactEntry) : Json :=
    let (lhs, rhs, formulaClass, degreeStatus) := match f.statement with
      | .implication l r | .equivalence l r | .nonImplication l r =>
        (conjJson l, conjJson r, Json.null, Json.null)
      | .conservation s w c | .nonConservation s w c =>
        (conjJson s, conjJson w, Json.str (toString c.name), Json.null)
      | .reducibility l r st | .nonReducibility l r st =>
        (Json.arr #[Json.str l.serialized], Json.arr #[Json.str r.serialized],
         Json.null, Json.str st.tag)
    Json.mkObj
      [("id", Json.str (toString f.id.name)),
       ("kind", Json.str f.statement.kindTag),
       ("context", factContextJson f.context),
       ("lhs", lhs),
       ("rhs", rhs),
       ("formulaClass", formulaClass),
       ("degreeStatus", degreeStatus),
       ("note", Json.str f.note),
       ("evidence", Json.arr ((snapshot.factEvidence.filter (·.fact == f.id)).map
         fun c => Json.mkObj
           [("context", Json.str (toString c.context.name)),
            ("certificate", nameJson c.thm),
            ("note", Json.str c.note)]))]
  let variantJson (v : StatementVariantEntry) : Json :=
    Json.mkObj
      [("id", Json.str v.id.serialized),
       ("concept", Json.str v.concept.serialized),
       ("layer", Json.str (toString v.layer.name)),
       ("interface", optNameJson v.interface?),
       ("interfaceModule", (v.interface?.map (moduleJson env)).getD Json.null),
       ("description", Json.str v.description),
       ("display", Json.mkObj [("label", Json.str (toString v.id.name))])]
  let problemJson (q : UniformProblemEntry) : Json :=
    Json.mkObj
      [("id", Json.str q.id.serialized),
       ("concept", Json.str q.concept.serialized),
       ("inputRepresentation", Json.str q.inputRepresentation),
       ("outputRepresentation", Json.str q.outputRepresentation),
       ("interface", optNameJson q.interface?),
       ("operation", Json.str q.operation.tag),
       ("uniformizes", (q.uniformizes?.map fun v => Json.str v.serialized).getD Json.null)]
  let nsJson (n : ExternalNamespaceEntry) : Json :=
    Json.mkObj
      [("id", Json.str (toString n.id.name)),
       ("description", Json.str n.description)]
  let refJson (r : ExternalRef) : Json :=
    Json.mkObj
      [("namespace", Json.str (toString r.ns.name)),
       ("key", Json.str r.key),
       ("relation", Json.str r.relation.tag),
       ("target", Json.mkObj
         [("kind", Json.str r.target.kindTag),
          ("id", Json.str s!"reverse-mathlib:{r.target.name}")])]
  -- Canonical section order is SERIALIZED-STRING order, not `Name.lt`: the two differ on
  -- names of different depth (`Name.lt` compares prefixes first), and the machine contract
  -- is what a JSON consumer can check by comparing the id strings.
  let concepts := cat.concepts.qsort fun a b => toString a.id.name < toString b.id.name
  let layers := cat.layers.qsort fun a b => toString a.id.name < toString b.id.name
  let variants := cat.variants.qsort fun a b => toString a.id.name < toString b.id.name
  let problems := cat.problems.qsort fun a b => toString a.id.name < toString b.id.name
  let namespaces := cat.namespaces.qsort fun a b => toString a.id.name < toString b.id.name
  let refs := cat.refs.qsort fun a b =>
    Name.lt a.ns.name b.ns.name || (a.ns.name == b.ns.name && (a.key < b.key ||
      (a.key == b.key && Name.lt a.target.name b.target.name)))
  let baseTheories := cat.baseTheories.qsort fun a b => toString a.id.name < toString b.id.name
  let formulaClasses := cat.formulaClasses.qsort fun a b =>
    toString a.id.name < toString b.id.name
  let reducibilityNotions := cat.reducibilityNotions.qsort fun a b =>
    toString a.id.name < toString b.id.name
  let facts := cat.facts.qsort fun a b => toString a.id.name < toString b.id.name
  let semanticContexts := cat.semanticContexts.qsort fun a b =>
    toString a.id.name < toString b.id.name
  let contextEntryJson (c : SemanticContextEntry) : Json :=
    Json.mkObj
      [("id", Json.str (toString c.id.name)),
       ("base", Json.str (toString c.base.name)),
       ("scope", Json.str c.scope.tag),
       ("layer", Json.str (toString c.layer.name)),
       ("contextDecl", nameJson c.contextDecl),
       ("description", Json.str c.description)]
  Json.mkObj
    [("schema", Json.str "reverse-mathlib.catalog/v5"),
     ("dependencies", Json.mkObj
       [("leanVersion", Json.str provenance.leanVersion),
        ("mathlibRevision", Json.str provenance.mathlibRevision)]),
     ("concepts", Json.arr (concepts.map conceptJson)),
     ("semanticLayers", Json.arr (layers.map layerJson)),
     ("statementVariants", Json.arr (variants.map variantJson)),
     ("uniformProblems", Json.arr (problems.map problemJson)),
     ("externalNamespaces", Json.arr (namespaces.map nsJson)),
     ("externalRefs", Json.arr (refs.map refJson)),
     ("baseTheories", Json.arr (baseTheories.map fun b => vocabJson b.id.name b.description)),
     ("formulaClasses", Json.arr (formulaClasses.map fun c => vocabJson c.id.name c.description)),
     ("reducibilityNotions", Json.arr
       (reducibilityNotions.map fun n => vocabJson n.id.name n.description)),
     ("facts", Json.arr (facts.map factJson)),
     ("semanticContexts", Json.arr (semanticContexts.map contextEntryJson)),
     ("ports", Json.arr (snapshot.ports.map portJson)),
     ("importedReductions", Json.arr
       (((importedReductionExt.getState env).qsort fun a b => a.id < b.id).map fun r =>
         Json.mkObj
           [("id", Json.str r.id),
            ("namespace", Json.str (toString r.ns.name)),
            ("repository", Json.str r.repository),
            ("revision", Json.str r.revision),
            ("external", Json.mkObj
              [("notion", Json.str r.notionKey),
               ("lhs", Json.str r.lhsKey),
               ("rhs", Json.str r.rhsKey)]),
            ("local", Json.mkObj
              [("notion", Json.str (toString r.notion.name)),
               ("lhs", Json.str s!"reverse-mathlib:{r.lhs.name}"),
               ("rhs", Json.str s!"reverse-mathlib:{r.rhs.name}")]),
            ("degree", Json.str r.degree.tag),
            ("status", Json.str r.status.tag),
            ("theorem", optStrJson r.theoremName?),
            ("mechanism", optStrJson r.mechanism?),
            ("downgraded", optStrJson r.downgraded?),
            ("note", Json.str r.note)])),
     ("backendEvidence", Json.arr
       (((backendEvidenceExt.getState env).qsort fun a b => a.id < b.id).map fun r =>
         let dataJson : Json := match r.data with
           | .contextRealization theory contextKey context contextPred direction
               realizationStatus =>
             Json.mkObj
               [("theory", Json.str theory),
                ("external", Json.mkObj [("contextKey", Json.str contextKey)]),
                ("local", Json.mkObj
                  [("context", Json.str (toString context.name)),
                   ("contextDecl", nameJson contextPred)]),
                ("direction", Json.str direction),
                ("realizationStatus", Json.str realizationStatus)]
           | .statementAdapter sentence capability variantKey variant adapterStatus =>
             Json.mkObj
               [("sentence", Json.str sentence),
                ("external", Json.mkObj [("variantKey", Json.str variantKey)]),
                ("local", Json.mkObj
                  [("variant", Json.str (toString variant.name)),
                   ("interface", nameJson capability)]),
                ("adapterStatus", Json.str adapterStatus)]
           | .calculusIdentity calculusId derivability soundness standardComparison =>
             Json.mkObj
               [("calculusId", Json.str calculusId),
                ("derivability", Json.str derivability),
                ("soundness", Json.str soundness),
                ("standardComparison", Json.str standardComparison)]
           | .calculusNonderivability calculusRecord sentenceAdapter calculusId theory
               sentence =>
             Json.mkObj
               [("calculusRecord", Json.str calculusRecord),
                ("sentenceAdapter", Json.str sentenceAdapter),
                ("calculusId", Json.str calculusId),
                ("theory", Json.str theory),
                ("sentence", Json.str sentence)]
           | .semanticCountermodel contextRealization sentenceAdapter theory sentence
               scope modelClass witnessProvenance witnessBase =>
             Json.mkObj
               [("contextRealization", Json.str contextRealization),
                ("sentenceAdapter", Json.str sentenceAdapter),
                ("theory", Json.str theory),
                ("sentence", Json.str sentence),
                ("scope", Json.str scope),
                ("modelClass", Json.str modelClass),
                ("witnessProvenance", Json.str witnessProvenance),
                ("witnessBase", Json.str witnessBase)]
         Json.mkObj
           [("id", Json.str r.id),
            ("kind", Json.str r.data.kindTag),
            ("namespace", Json.str (toString r.ns.name)),
            ("source", Json.mkObj
              [("repository", Json.str r.repository),
               ("exportRevision", Json.str r.revision),
               ("artifactRevision", Json.str r.artifactRevision),
               ("artifactPath", Json.str r.artifactPath),
               ("toolchain", Json.str r.toolchain),
               ("dependencies", Json.mkObj
                 [("reverse-mathlib", Json.str r.rmRevision),
                  ("Foundation", Json.str r.foundationRevision),
                  ("mathlib", Json.str r.mathlibRevision)])]),
            ("checking", Json.mkObj
              [("mechanism", optStrJson r.mechanism?),
               ("audit", optStrJson r.audit?),
               ("allowedAxioms", Json.arr (r.allowedAxioms.map Json.str))]),
            ("export", Json.str r.exportName),
            ("theorem", optStrJson r.theoremName?),
            ("status", Json.str r.status.tag),
            ("downgraded", optStrJson r.downgraded?),
            ("data", dataJson),
            ("display", Json.mkObj [("rendered", Json.str r.render)])])),
     ("corpus", corpusJson env),
     ("ambientGraph", Json.mkObj
       [("comment", Json.str "kernel-checked relative certificates in unrestricted Lean; \
          NOT reverse-mathematics implications"),
        ("nodes", Json.arr (nodes.map nodeJson)),
        ("edges", Json.arr (snapshot.ambientEdges.map edgeJson))])]

/-- `#rm_export_catalog "path"`: write the canonical direct-catalog JSON. Parent directories
are created; the file ends with a newline. -/
elab "#rm_export_catalog " path:str : command => do
  discard requireCleanCatalog  -- a conflicted conceptual catalog must never export
  let snapshot := CatalogSnapshot.ofEnv (← getEnv)
  let provenance ← BuildProvenance.read
  let p := System.FilePath.mk path.getString
  if let some dir := p.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile p ((snapshot.toJson (← getEnv) provenance).pretty ++ "\n")
  logInfo s!"rm_export_catalog: wrote {snapshot.conceptCatalog.concepts.size} concept(s), \
    {snapshot.conceptCatalog.variants.size} variant(s), \
    {snapshot.conceptCatalog.facts.size} fact(s), {snapshot.ports.size} port(s), \
    {snapshot.ambientEdges.size} ambient edge(s) to {path.getString}"

end ReverseMathlib.Meta
