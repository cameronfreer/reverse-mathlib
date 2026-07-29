/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Report

/-!
# The evidence registry

Records reverse-mathematics *principles* (an open vocabulary of `PrincipleId`s — plain names,
never a closed inductive, so new principles never migrate a central type) and *ports* (a
relationship between a mathlib declaration and a statement in this repository), each carrying
**multidimensional evidence**: kind × bound direction × verification × proof ambient × semantic
scope. Evidence is never ordinal — a reversal is `direction := lower`, not a maturity stage.

Honesty rules, enforced at registration or rendering:

* **Proof ambient ≠ semantic scope.** An ambient-Lean relative proof carries *no* RM semantic
  scope (registration rejects a scope on ambient-`lean` evidence); `semanticImplication`
  evidence requires an explicit scope. Scope is never defaulted or silently escalated.
* **Certificates carry their meaning in their type.** A `relativeProof` evidence record cites a
  `RelativeCertificate assumption conclusion`; registration checks, up to definitional
  equality, that `assumption` is the registered principle's interface and `conclusion` is the
  port's statement — a bare axiom-audited reference (which `True.intro` would pass) is not a
  certificate. Kernel-checked citations are additionally swept by `collectAxioms` against the
  standard three axioms.
* **Rendering condition for a certified RM bound** (nothing in Milestone 1 reaches it):
  `syntacticDerivation` directly supports the corresponding subsystem claim;
  `semanticImplication` requires scope `omegaModels` or `allModels` — `fullStandardModel`
  never suffices for a subsystem bound by itself; `fragmentCheck` alone only establishes
  membership in a fragment and renders as an RM bound only when paired with a backend-checked
  fragment-to-subsystem interpretation certificate (not yet representable, hence never
  rendered). Everything else prints `pending`/`UNVERIFIED`, and unknown prints `unknown`.
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- An open principle identifier: a plain name. The vocabulary of principles is open on
purpose — registering a new principle must never require changing a central inductive type or
migrating serialized metadata. -/
structure PrincipleId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

instance : ToString PrincipleId := ⟨fun p => toString p.name⟩

/-- What kind of evidence a record is. Orthogonal to `BoundDirection`, `Verification`,
`ProofAmbient`, and `SemanticScope`. -/
inductive EvidenceKind where
  /-- A raw dependency audit (`#rm_deps`-style facts). -/
  | dependencyAudit
  /-- A frontier cut exhibited in a proof's dependency graph. -/
  | frontierSlice
  /-- A relative Lean factorization: a theorem deriving the port's statement from a
  principle's interface taken as a hypothesis. -/
  | relativeProof
  /-- Membership of a proof in a checked fragment. Alone this never renders as an RM bound. -/
  | fragmentCheck
  /-- A semantic implication over a class of models; requires an explicit scope. -/
  | semanticImplication
  /-- A syntactic derivation in an object subsystem. -/
  | syntacticDerivation
  deriving Inhabited, Repr, BEq

/-- Which direction of a bound the evidence addresses. A reversal is `lower`, not a separate
final stage. -/
inductive BoundDirection where
  /-- Upper-bound evidence. -/
  | upper
  /-- Lower-bound evidence (a reversal). -/
  | lower
  /-- Exact-calibration evidence. -/
  | exact
  deriving Inhabited, Repr, BEq

/-- How the evidence is verified. -/
inductive Verification where
  /-- Cited from the literature or asserted; always rendered `UNVERIFIED`. -/
  | claimed
  /-- Checked by the Lean kernel in this repository. -/
  | kernelChecked
  /-- Checked by a reverse-mathematics backend (none exists yet). -/
  | backendChecked
  deriving Inhabited, Repr, BEq

/-- The ambient system the evidence's proof lives in. Distinct from semantic scope: an
ambient-Lean factorization over standard objects says nothing about models. -/
inductive ProofAmbient where
  /-- Unrestricted Lean over standard objects. -/
  | lean
  /-- A checked fragment, identified by principle id. -/
  | checkedFragment (id : PrincipleId)
  /-- Model-relative semantics (e.g. ω-models). -/
  | modelSemantics
  /-- An object-language subsystem. -/
  | objectTheory
  deriving Inhabited, Repr, BEq

/-- Semantic scope of model-relative evidence. Never defaulted, never silently escalated. -/
inductive SemanticScope where
  /-- The full standard model `(ℕ, 𝒫(ℕ))` only. Never suffices for a subsystem bound. -/
  | fullStandardModel
  /-- All ω-models (standard first-order part, restricted set part). -/
  | omegaModels
  /-- All models of the base theory. -/
  | allModels
  deriving Inhabited, Repr, BEq

/-- A typed relative certificate: the claimed relationship is part of the checked type, so an
unrelated kernel-checked theorem cannot masquerade as a certificate. -/
structure RelativeCertificate (assumption conclusion : Prop) : Prop where
  /-- The factorization itself. -/
  proof : assumption → conclusion

/-- One piece of evidence attached to a port. -/
structure EvidenceRecord where
  /-- What kind of evidence this is. -/
  kind : EvidenceKind
  /-- Which bound direction it addresses. -/
  direction : BoundDirection
  /-- How it is verified. -/
  verification : Verification
  /-- The ambient system of its proof. -/
  ambient : ProofAmbient
  /-- Semantic scope, when the evidence is model-relative. `none` for ambient-Lean evidence. -/
  scope? : Option SemanticScope := none
  /-- The cited certificate or theorem, when verified in Lean. -/
  thm? : Option Name := none
  /-- For `relativeProof`: the principle taken as hypothesis. -/
  assumes? : Option PrincipleId := none
  /-- Free-text qualifier. -/
  note : String := ""
  deriving Inhabited, Repr, BEq

/-- A registered principle. -/
structure PrincipleEntry where
  /-- The open identifier. -/
  id : PrincipleId
  /-- Informal description. -/
  description : String
  /-- The Lean interface (a `Prop`-valued declaration), when formalized. -/
  interface? : Option Name := none
  /-- Claimed classical classification, literature only; always rendered `UNVERIFIED`. -/
  claimedClassical? : Option String := none
  deriving Inhabited, Repr, BEq

/-- Relation between a mathlib declaration and a port. -/
inductive PortRelation where
  /-- The port's proof is an analogue of the source proof. -/
  | proofAnalogue
  /-- The port's proof reuses the source proof's architecture with boundaries replaced. -/
  | minedArchitecture
  /-- The port is an exact specialization of the source statement. -/
  | exactSpecialization
  /-- Conceptual relationship only. -/
  | conceptualAnalogue
  deriving Inhabited, Repr, BEq

/-- A registered port. -/
structure PortEntry where
  /-- Registry key, unique. -/
  id : Name
  /-- Counterpart declaration in mathlib, if any. -/
  mathlibDecl? : Option Name := none
  /-- The statement in this repository, if formalized. -/
  portDecl? : Option Name := none
  /-- Relation to the mathlib counterpart. -/
  relation : PortRelation
  /-- Claimed classical classification, literature only; always rendered `UNVERIFIED`. -/
  claimedClassical? : Option String := none
  /-- Free-text notes. -/
  note : String := ""
  /-- The attached evidence. -/
  evidence : Array EvidenceRecord := #[]
  deriving Inhabited, Repr, BEq

initialize principleExt :
    SimplePersistentEnvExtension PrincipleEntry (Array PrincipleEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

initialize portExt : SimplePersistentEnvExtension PortEntry (Array PortEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

/-! ## Registration-time validation -/

/-- Standard axioms allowed for kernel-checked citations. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Reject a kernel-checked citation that depends on a non-standard axiom. -/
def checkStandardAxioms (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms n
  for a in axs do
    unless standardAxioms.contains a do
      throwError "registry: '{n}' depends on non-standard axiom '{a}'"

/-- Check that `cert` has type `RelativeCertificate assumption conclusion` (up to definitional
equality) for the registered principle interface and port statement. This is what makes a
citation a *certificate*: the relationship is part of the checked type. -/
def checkCertificateType (cert assumption conclusion : Name) : CommandElabM Unit := do
  liftTermElabM do
    let info ← getConstInfo cert
    let ty ← Meta.whnfR info.type
    let fn := ty.getAppFn
    unless fn.isConstOf ``RelativeCertificate do
      throwError "registry: '{cert}' does not have type 'RelativeCertificate _ _' \
        (found '{ty}'); a relativeProof citation must be a typed certificate"
    let args := ty.getAppArgs
    unless args.size == 2 do
      throwError "registry: unexpected arity in certificate type '{ty}'"
    unless ← Meta.isDefEq args[0]! (mkConst assumption) do
      throwError "registry: certificate '{cert}' assumes '{args[0]!}', which is not \
        definitionally the registered interface '{assumption}' of the cited principle"
    unless ← Meta.isDefEq args[1]! (mkConst conclusion) do
      throwError "registry: certificate '{cert}' concludes '{args[1]!}', which is not \
        definitionally the registered port statement '{conclusion}'"

/-- Look up a registered principle by id. -/
def findPrinciple? (env : Environment) (id : PrincipleId) : Option PrincipleEntry :=
  (principleExt.getState env).find? (·.id == id)

/-- Look up a registered port by id. -/
def findPort? (env : Environment) (id : Name) : Option PortEntry :=
  (portExt.getState env).find? (·.id == id)

/-- Validate one evidence record against the registry and the cited port statement. -/
def validateEvidence (e : EvidenceRecord) (portDecl? : Option Name) : CommandElabM Unit := do
  if e.ambient == .lean && e.scope?.isSome then
    throwError "registry: ambient-Lean evidence carries no RM semantic scope; remove the \
      scope or change the ambient"
  if e.kind == .semanticImplication && e.scope?.isNone then
    throwError "registry: semanticImplication evidence requires an explicit scope \
      (fullStandardModel | omegaModels | allModels); scope is never defaulted"
  if e.verification == .kernelChecked then
    let some thm := e.thm?
      | throwError "registry: kernelChecked evidence must cite a theorem (via ...)"
    checkStandardAxioms thm
  if e.verification == .backendChecked then
    throwError "registry: no backend exists yet; backendChecked evidence cannot be registered"
  if e.kind == .relativeProof && e.verification == .kernelChecked then
    let some thm := e.thm?
      | throwError "registry: relativeProof evidence must cite its certificate"
    let some assumes := e.assumes?
      | throwError "registry: relativeProof evidence must name the assumed principle \
        (assumes ...)"
    let some pentry := findPrinciple? (← getEnv) assumes
      | throwError "registry: unknown principle '{assumes}'"
    let some interface := pentry.interface?
      | throwError "registry: principle '{assumes}' has no registered Lean interface"
    let some portDecl := portDecl?
      | throwError "registry: relativeProof evidence requires the port to have a registered \
        statement"
    checkCertificateType thm interface portDecl

/-! ## Registration commands -/

/-- Resolve an identifier to a global constant. -/
private def resolveConst (id : TSyntax `ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

/-- `rm_principle id where description := "…" interface := SomeProp
claimedClassical := "…"`: register a principle. The interface must be a `Prop`-valued
declaration; the claimed classification is literature-only and always renders `UNVERIFIED`. -/
syntax (name := rmPrincipleCmd) "rm_principle " ident " where "
  &"description" " := " str
  &"interface" " := " ident
  (&"claimedClassical" " := " str)? : command

@[command_elab rmPrincipleCmd]
def elabRmPrinciple : CommandElab := fun stx => do
  let id : PrincipleId := ⟨stx[1].getId⟩
  let description := (⟨stx[5]⟩ : TSyntax `str).getString
  let interface ← resolveConst ⟨stx[8]⟩
  let claimed? : Option String :=
    if stx[9].getNumArgs == 0 then none
    else some ((⟨stx[9][2]⟩ : TSyntax `str).getString)
  if (findPrinciple? (← getEnv) id).isSome then
    throwError "registry: duplicate principle id '{id}'"
  liftTermElabM do
    let info ← getConstInfo interface
    unless info.type.isProp do
      throwError "registry: interface '{interface}' must be a Prop-valued declaration"
  modifyEnv fun env => principleExt.addEntry env
    { id, description, interface? := some interface, claimedClassical? := claimed? }

/-- One evidence line of a `revmath_port` command:
`evidence <kind> <direction> <verification> <ambient> [scope <s>] [via <thm>] [assumes <p>]
[note "…"]`. -/
syntax rmEvidenceLine := &"evidence" ident ident ident ident (&"scope" ident)?
  (&"via" ident)? (&"assumes" ident)? (&"note" str)?

/-- `revmath_port id where mathlib := … port := … relation := … …`: register a port with its
evidence. All cited names must resolve; kernel-checked citations are axiom-swept; typed
certificates are matched against the registered principle interface and port statement up to
definitional equality. -/
syntax (name := revmathPortCmd) "revmath_port " ident " where "
  &"mathlib" " := " ident
  &"port" " := " ident
  &"relation" " := " ident
  (&"claimedClassical" " := " str)?
  (&"note" " := " str)?
  (rmEvidenceLine)* : command

private def parseKind (stx : Syntax) : CommandElabM EvidenceKind :=
  match stx.getId with
  | `dependencyAudit => pure .dependencyAudit
  | `frontierSlice => pure .frontierSlice
  | `relativeProof => pure .relativeProof
  | `fragmentCheck => pure .fragmentCheck
  | `semanticImplication => pure .semanticImplication
  | `syntacticDerivation => pure .syntacticDerivation
  | k => throwErrorAt stx "registry: unknown evidence kind '{k}' (expected dependencyAudit | \
      frontierSlice | relativeProof | fragmentCheck | semanticImplication | \
      syntacticDerivation)"

private def parseDirection (stx : Syntax) : CommandElabM BoundDirection :=
  match stx.getId with
  | `upper => pure .upper
  | `lower => pure .lower
  | `exact => pure .exact
  | d => throwErrorAt stx "registry: unknown bound direction '{d}' (expected upper | lower | \
      exact)"

private def parseVerification (stx : Syntax) : CommandElabM Verification :=
  match stx.getId with
  | `claimed => pure .claimed
  | `kernelChecked => pure .kernelChecked
  | `backendChecked => pure .backendChecked
  | v => throwErrorAt stx "registry: unknown verification '{v}' (expected claimed | \
      kernelChecked | backendChecked)"

private def parseAmbient (stx : Syntax) : CommandElabM ProofAmbient :=
  match stx.getId with
  | `lean => pure .lean
  | `modelSemantics => pure .modelSemantics
  | `objectTheory => pure .objectTheory
  | a => throwErrorAt stx "registry: unknown ambient '{a}' (expected lean | modelSemantics | \
      objectTheory; checkedFragment is registered programmatically)"

private def parseScope (stx : Syntax) : CommandElabM SemanticScope :=
  match stx.getId with
  | `fullStandardModel => pure .fullStandardModel
  | `omegaModels => pure .omegaModels
  | `allModels => pure .allModels
  | s => throwErrorAt stx "registry: unknown scope '{s}' (expected fullStandardModel | \
      omegaModels | allModels)"

private def parseRelation (stx : Syntax) : CommandElabM PortRelation :=
  match stx.getId with
  | `proofAnalogue => pure .proofAnalogue
  | `minedArchitecture => pure .minedArchitecture
  | `exactSpecialization => pure .exactSpecialization
  | `conceptualAnalogue => pure .conceptualAnalogue
  | r => throwErrorAt stx "registry: unknown relation '{r}' (expected proofAnalogue | \
      minedArchitecture | exactSpecialization | conceptualAnalogue)"

private def optArg (stx : Syntax) (i : Nat) : Option Syntax :=
  if stx.getNumArgs == 0 then none else some stx[i]

@[command_elab revmathPortCmd]
def elabRevmathPort : CommandElab := fun stx => do
  let id := stx[1].getId
  let mathlibDecl ← resolveConst ⟨stx[5]⟩
  let portDecl ← resolveConst ⟨stx[8]⟩
  let relation ← parseRelation stx[11]
  let claimed? : Option String :=
    (optArg stx[12] 2).map fun s => (⟨s⟩ : TSyntax `str).getString
  let note : String :=
    ((optArg stx[13] 2).map fun s => (⟨s⟩ : TSyntax `str).getString).getD ""
  let mut evidence : Array EvidenceRecord := #[]
  for ev in stx[14].getArgs do
    let kind ← parseKind ev[1]
    let direction ← parseDirection ev[2]
    let verification ← parseVerification ev[3]
    let ambient ← parseAmbient ev[4]
    let scope? ← (optArg ev[5] 1).mapM parseScope
    let thm? ← (optArg ev[6] 1).mapM fun s => resolveConst ⟨s⟩
    let assumes? : Option PrincipleId := (optArg ev[7] 1).map fun s => ⟨s.getId⟩
    let evNote : String :=
      ((optArg ev[8] 1).map fun s => (⟨s⟩ : TSyntax `str).getString).getD ""
    let rec' : EvidenceRecord :=
      { kind, direction, verification, ambient, scope?, thm?, assumes?, note := evNote }
    validateEvidence rec' (some portDecl)
    evidence := evidence.push rec'
  if (findPort? (← getEnv) id).isSome then
    throwError "registry: duplicate port id '{id}'"
  modifyEnv fun env => portExt.addEntry env
    { id, mathlibDecl? := some mathlibDecl, portDecl? := some portDecl, relation,
      claimedClassical? := claimed?, note, evidence }

/-! ## Rendering (fail-closed) -/

/-- Whether an evidence record qualifies, by the rendering condition, to support a certified RM
bound. `fragmentCheck` alone never qualifies (it needs a backend-checked fragment-to-subsystem
certificate, which is not yet representable), `semanticImplication` needs a non-trivial scope,
and nothing `claimed` ever qualifies. -/
def EvidenceRecord.supportsCertifiedBound (e : EvidenceRecord) : Bool :=
  e.verification != .claimed &&
    (e.kind == .syntacticDerivation ||
      (e.kind == .semanticImplication &&
        (e.scope? == some .omegaModels || e.scope? == some .allModels)))

/-- Render an ambient. -/
def ProofAmbient.render : ProofAmbient → String
  | .lean => "unrestricted Lean over standard ℕ"
  | .checkedFragment id => s!"checked fragment {id}"
  | .modelSemantics => "model semantics"
  | .objectTheory => "object theory"

/-- Render a scope option; `none` prints `none`, honestly. -/
def renderScope : Option SemanticScope → String
  | none => "none"
  | some .fullStandardModel => "full standard model only"
  | some .omegaModels => "all ω-models"
  | some .allModels => "all models"

/-- Render an evidence kind. -/
def EvidenceKind.render : EvidenceKind → String
  | .dependencyAudit => "dependency audit"
  | .frontierSlice => "frontier slice"
  | .relativeProof => "relative Lean factorization"
  | .fragmentCheck => "fragment membership"
  | .semanticImplication => "semantic implication"
  | .syntacticDerivation => "syntactic derivation"

/-- Render a verification. -/
def Verification.render : Verification → String
  | .claimed => "claimed (UNVERIFIED)"
  | .kernelChecked => "kernel checked"
  | .backendChecked => "backend checked"

/-- Render a direction. -/
def BoundDirection.render : BoundDirection → String
  | .upper => "upper"
  | .lower => "lower"
  | .exact => "exact"

/-- Render a relation. -/
def PortRelation.render : PortRelation → String
  | .proofAnalogue => "proof analogue"
  | .minedArchitecture => "proof analogue / mined architecture"
  | .exactSpecialization => "exact specialization"
  | .conceptualAnalogue => "conceptual analogue"

/-- Render one evidence record as indented lines. -/
def EvidenceRecord.render (e : EvidenceRecord) : Array String := Id.run do
  let mut lines := #[s!"  {e.direction.render} · {e.kind.render}: {e.verification.render}"]
  if let some thm := e.thm? then
    let assumes := match e.assumes? with
      | some p => s!" (assumes {p})"
      | none => ""
    lines := lines.push s!"    certificate: {thm}{assumes}"
  lines := lines.push s!"    ambient: {e.ambient.render}; RM semantic scope: {renderScope e.scope?}"
  unless e.note.isEmpty do
    lines := lines.push s!"    note: {e.note}"
  return lines

/-- Render a port entry, fail-closed: claimed classifications always carry `UNVERIFIED`, a
missing backend certificate prints `pending`, a missing lower bound prints `pending`. -/
def PortEntry.render (p : PortEntry) : String := Id.run do
  let mut lines := #[s!"{p.id}"]
  lines := lines.push s!"  mathlib: {(p.mathlibDecl?.map toString).getD "none"}"
  lines := lines.push s!"  port: {(p.portDecl?.map toString).getD "none"}"
  lines := lines.push s!"  source relation: {p.relation.render}"
  for e in p.evidence do
    lines := lines ++ e.render
  match p.claimedClassical? with
  | some c => lines := lines.push s!"  candidate classical classification: {c} [claimed, UNVERIFIED]"
  | none => lines := lines.push s!"  candidate classical classification: unknown"
  if p.evidence.any (·.supportsCertifiedBound) then
    lines := lines.push s!"  certified RM bound: see qualifying evidence above"
  else
    lines := lines.push s!"  backend RM certificate: pending"
  unless p.evidence.any fun e =>
      (e.direction == .lower || e.direction == .exact) && e.verification != .claimed do
    lines := lines.push s!"  exact lower bound: pending"
  unless p.note.isEmpty do
    lines := lines.push s!"  note: {p.note}"
  return "\n".intercalate lines.toList

/-- Render a principle entry. -/
def PrincipleEntry.render (p : PrincipleEntry) : String := Id.run do
  let mut lines := #[s!"{p.id}"]
  lines := lines.push s!"  {p.description}"
  lines := lines.push s!"  interface: {(p.interface?.map toString).getD "none"}"
  match p.claimedClassical? with
  | some c => lines := lines.push s!"  claimed classical classification: {c} [claimed, UNVERIFIED]"
  | none => lines := lines.push s!"  claimed classical classification: unknown"
  return "\n".intercalate lines.toList

/-- `#revmath_registry`: print every registered principle and port, sorted by id. -/
elab "#revmath_registry" : command => do
  let env ← getEnv
  let principles := (principleExt.getState env).qsort fun a b => Name.lt a.id.name b.id.name
  let ports := (portExt.getState env).qsort fun a b => Name.lt a.id b.id
  let pl := principles.toList.map PrincipleEntry.render
  let ql := ports.toList.map PortEntry.render
  logInfo <| "\n".intercalate
    ([s!"principles ({principles.size}):"] ++ pl ++ [s!"ports ({ports.size}):"] ++ ql)

/-- `#revmath_port? id`: look up a port by registry id, mathlib declaration, or port
declaration. -/
elab "#revmath_port? " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let resolved? := (← liftCoreM <| try
    pure (some (← realizeGlobalConstNoOverload id)) catch _ => pure none)
  let hit? := (portExt.getState env).find? fun p =>
    p.id == n || p.mathlibDecl? == resolved? || p.portDecl? == resolved? ||
      p.mathlibDecl? == some n || p.portDecl? == some n
  match hit? with
  | some p => logInfo p.render
  | none => throwErrorAt id "registry: no port registered under '{n}'"

/-- `#revmath_stats`: the honest scoreboard — evidence counts by verification, and how many
certified RM bounds exist (in Milestone 1: zero, by construction). -/
elab "#revmath_stats" : command => do
  let env ← getEnv
  let principles := principleExt.getState env
  let ports := portExt.getState env
  let evs := ports.flatMap (·.evidence)
  let count (v : Verification) := evs.filter (·.verification == v) |>.size
  let certified := evs.filter (·.supportsCertifiedBound) |>.size
  logInfo <| s!"principles: {principles.size}; ports: {ports.size}; evidence: {evs.size} \
    ({count .kernelChecked} kernel checked, {count .claimed} claimed, \
    {count .backendChecked} backend checked); certified RM bounds: {certified}"

end ReverseMathlib.Meta
