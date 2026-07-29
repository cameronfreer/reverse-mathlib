/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry

/-!
# Deterministic catalog export

`#rm_export_catalog "path"` writes the canonical direct-catalog JSON
(`reverse-mathlib.catalog/v0`) extracted from the **elaborated environment's persistent
extension state** — never by parsing Lean source or scraping human-readable command output.
The persistent extensions have already resolved names and validated certificates; they are the
right extraction point.

Canonical-file properties:

* IDs are canonical strings (declaration and registry names), never generated numerics;
* every array is deterministically sorted;
* **no timestamp** — the canonical file depends only on the environment and pin;
* evidence is exported in full, never collapsed to a maturity score;
* display metadata (labels) is separate from mathematical fields;
* source locations are module names, never absolute build-machine paths;
* build provenance records the Lean version and the pinned mathlib revision (or the explicit
  string `"unavailable"`).

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
  /-- Registered principles, sorted by id. -/
  principles : Array PrincipleEntry
  /-- Registered ports, sorted by id. -/
  ports : Array PortEntry
  /-- Ambient-factorization edges, sorted by (source, target, port, evidenceIdx). -/
  ambientEdges : Array AmbientEdge

/-- Derive the ambient-factorization edges of one port. Direction-aware: `upper` maps
interface → port statement, `lower` maps port statement → interface, `exact` contributes both
directions. Only kernel-checked `relativeProof` evidence with resolvable endpoints yields
edges. -/
def ambientEdgesOf (principles : Array PrincipleEntry) (p : PortEntry) :
    Array AmbientEdge := Id.run do
  let mut edges := #[]
  let some portDecl := p.portDecl? | return #[]
  let mut i := 0
  for e in p.evidence do
    if e.kind == .relativeProof && e.verification == .kernelChecked then
      if let (some cert, some assumes) := (e.thm?, e.assumes?) then
        if let some pentry := principles.find? (·.id == assumes) then
          if let some interface := pentry.interface? then
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

/-- Extract the snapshot from an elaborated environment. Deterministic: all arrays sorted. -/
def CatalogSnapshot.ofEnv (env : Environment) : CatalogSnapshot :=
  let principles := (principleExt.getState env).qsort fun a b => Name.lt a.id.name b.id.name
  let ports := (portExt.getState env).qsort fun a b => Name.lt a.id b.id
  let edges := (ports.flatMap (ambientEdgesOf principles)).qsort fun a b =>
    Name.lt a.source b.source ||
      (a.source == b.source && (Name.lt a.target b.target ||
        (a.target == b.target && (Name.lt a.port b.port ||
          (a.port == b.port && a.evidenceIdx < b.evidenceIdx)))))
  { principles, ports, ambientEdges := edges }

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

/-- Render an evidence record in full — never collapsed to a maturity score. -/
def evidenceJson (e : EvidenceRecord) : Json :=
  Json.mkObj
    [("kind", Json.str e.kind.render),
     ("direction", Json.str e.direction.render),
     ("verification", Json.str e.verification.render),
     ("ambient", Json.str e.ambient.render),
     ("scope", Json.str (renderScope e.scope?)),
     ("theory", optNameJson (e.theory?.map (·.name))),
     ("certificate", optNameJson e.thm?),
     ("assumes", optNameJson (e.assumes?.map (·.name))),
     ("note", Json.str e.note)]

/-- Serialize the snapshot with provenance to canonical JSON. -/
def CatalogSnapshot.toJson (snapshot : CatalogSnapshot) (env : Environment)
    (provenance : BuildProvenance) : Json :=
  let principleJson (p : PrincipleEntry) : Json :=
    Json.mkObj
      [("id", nameJson p.id.name),
       ("description", Json.str p.description),
       ("interface", optNameJson p.interface?),
       ("interfaceModule", (p.interface?.map (moduleJson env)).getD Json.null),
       ("literatureNote", optStrJson p.claimedClassical?),
       ("display", Json.mkObj [("label", Json.str (toString p.id.name))])]
  let portJson (p : PortEntry) : Json :=
    Json.mkObj
      [("id", nameJson p.id),
       ("mathlibDecl", optNameJson p.mathlibDecl?),
       ("mathlibModule", (p.mathlibDecl?.map (moduleJson env)).getD Json.null),
       ("portDecl", optNameJson p.portDecl?),
       ("relation", Json.str p.relation.render),
       ("literatureNote", optStrJson p.claimedClassical?),
       ("note", Json.str p.note),
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
  let nodes := (nodes.foldl (init := ({} : NameSet)) fun s n => s.insert n).toArray
  let nodeJson (n : Name) : Json :=
    Json.mkObj
      [("id", nameJson n),
       ("module", moduleJson env n),
       ("display", Json.mkObj [("label", Json.str (toString (n.componentsRev.headD n)))])]
  Json.mkObj
    [("schema", Json.str "reverse-mathlib.catalog/v0"),
     ("dependencies", Json.mkObj
       [("leanVersion", Json.str provenance.leanVersion),
        ("mathlibRevision", Json.str provenance.mathlibRevision)]),
     ("principles", Json.arr (snapshot.principles.map principleJson)),
     ("ports", Json.arr (snapshot.ports.map portJson)),
     ("ambientGraph", Json.mkObj
       [("comment", Json.str "kernel-checked relative certificates in unrestricted Lean; \
          NOT reverse-mathematics implications"),
        ("nodes", Json.arr (nodes.map nodeJson)),
        ("edges", Json.arr (snapshot.ambientEdges.map edgeJson))])]

/-- `#rm_export_catalog "path"`: write the canonical direct-catalog JSON. Parent directories
are created; the file ends with a newline. -/
elab "#rm_export_catalog " path:str : command => do
  let snapshot := CatalogSnapshot.ofEnv (← getEnv)
  let provenance ← BuildProvenance.read
  let p := System.FilePath.mk path.getString
  if let some dir := p.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile p ((snapshot.toJson (← getEnv) provenance).pretty ++ "\n")
  logInfo s!"rm_export_catalog: wrote {snapshot.principles.size} principle(s), \
    {snapshot.ports.size} port(s), {snapshot.ambientEdges.size} ambient edge(s) to \
    {path.getString}"

end ReverseMathlib.Meta
