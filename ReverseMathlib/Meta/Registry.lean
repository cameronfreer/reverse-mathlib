/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Report
import ReverseMathlib.Meta.Concepts

/-!
# The evidence registry

Records the evidence layer over the conceptual catalog (`ReverseMathlib.Meta.Concepts`):
*ports* relate a mathlib declaration to an **exact statement variant** in this repository,
each carrying
**multidimensional evidence**: kind × bound direction × verification × proof ambient × semantic
scope. Evidence is never ordinal — a reversal is `direction := lower`, not a maturity stage.

Honesty rules, enforced at registration or rendering:

* **Proof ambient ≠ semantic scope.** An ambient-Lean relative proof carries *no* RM semantic
  scope (registration rejects a scope on ambient-`lean` evidence); `semanticImplication`
  evidence requires an explicit scope. Scope is never defaulted or silently escalated.
* **Certificates carry their meaning in their type, direction-aware.** A kernel-checked
  `relativeProof` record cites a typed certificate matched up to definitional equality:
  `RelativeCertificate interface port` for `upper` evidence, `RelativeCertificate port
  interface` for `lower`, `interface ↔ port` for `exact` — a bare axiom-audited reference
  (which `True.intro` would pass) is never a certificate. Kernel-checked citations of any
  *other* kind (semantic, syntactic, fragment, audit) are rejected outright until typed schemas
  exist for them. Kernel-checked citations are additionally swept by `collectAxioms` against
  the standard three axioms, and evidence kind must agree with its ambient.
* **Certified claims carry an explicit scope** (`CertifiedClaimScope`): ambient factorization,
  checked-fragment membership, ω-models, all models, and syntactic derivation render
  separately, and no scope is ever escalated automatically — an all-ω-model theorem is not a
  syntactic subsystem theorem, and even an all-model semantic result stays distinct until an
  explicit soundness/completeness bridge upgrades it. Only ω-model, all-model, and syntactic
  claims count as RM bounds (nothing in Milestone 1 produces one); claimed/literature evidence
  never produces a claim, so it can never suppress a `pending` line. Everything else prints
  `pending`/`UNVERIFIED`, and unknown prints `unknown`.
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- An open checked-fragment identifier. A checked fragment is not a mathematical statement,
so it gets its own identifier — never a statement-variant id. -/
structure FragmentId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

instance : ToString FragmentId := ⟨fun p => toString p.name⟩

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
  /-- A checked fragment, identified by its own fragment id (never a statement-variant id:
  a fragment is not a mathematical statement). -/
  | checkedFragment (id : FragmentId)
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
unrelated kernel-checked theorem cannot masquerade as a certificate. Direction-aware use:
`RelativeCertificate P T` (principle implies port statement) is accepted only as an **upper**
certificate; lower evidence requires `RelativeCertificate T P`; exact evidence requires an
`Iff` between the two. -/
structure RelativeCertificate (assumption conclusion : Prop) : Prop where
  /-- The factorization itself. -/
  proof : assumption → conclusion

/-- An open theory identifier (for future syntactic-derivation claims), open for the same
reason as `ConceptId`. -/
structure TheoryId where
  /-- The identifying name. -/
  name : Name
  deriving Inhabited, Repr, BEq, Hashable

/-- The scope of a *certified* claim. Scopes are never escalated automatically: a theorem valid
in all ω-models is a certified ω-model result, not a syntactic subsystem theorem; even a valid
all-model semantic result stays distinct until an explicit soundness/completeness bridge
upgrades it. -/
inductive CertifiedClaimScope where
  /-- An ambient-Lean factorization (a `RelativeCertificate`). Not an RM bound. -/
  | ambientFactorization
  /-- Membership in a checked fragment. Not an RM bound without a fragment-to-subsystem
  certificate. -/
  | checkedFragment
  /-- Valid in all ω-models. -/
  | omegaModels
  /-- Valid in all models of the base theory. -/
  | allModels
  /-- A syntactic derivation in the named theory. -/
  | syntacticDerivation (theory : TheoryId)
  deriving Inhabited, Repr, BEq

/-- Whether a certified claim scope supports a reverse-mathematics bound. -/
def CertifiedClaimScope.isRMBound : CertifiedClaimScope → Bool
  | .omegaModels | .allModels | .syntacticDerivation _ => true
  | .ambientFactorization | .checkedFragment => false

/-- A certified claim extracted from validated evidence: scope × direction × the index of the
evidence record it came from. -/
structure CertifiedClaim where
  /-- The claim's scope. -/
  scope : CertifiedClaimScope
  /-- The bound direction the claim addresses. -/
  direction : BoundDirection
  /-- Index of the originating record in the port's evidence array. -/
  evidence : Nat
  deriving Inhabited, Repr, BEq

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
  /-- Semantic scope; only `semanticImplication` evidence may carry one. -/
  scope? : Option SemanticScope := none
  /-- For `syntacticDerivation`: the object theory, through this dedicated field (never through
  the scope). -/
  theory? : Option TheoryId := none
  /-- The cited certificate; only `kernelChecked` evidence may carry one (literature is cited
  in the note). -/
  thm? : Option Name := none
  /-- For `relativeProof` (only): the exact statement variant taken as hypothesis — required
  even for claimed records, so a malformed unverified record cannot be registered. The cited
  variant must own a Prop-valued Lean interface for kernel-checked evidence. -/
  assumes? : Option StatementVariantId := none
  /-- Free-text qualifier. -/
  note : String := ""
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
  /-- The exact statement variant this port targets. -/
  target : StatementVariantId
  /-- The port statement — derived from the target variant's Lean interface at registration,
  so the two can never drift. -/
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
equality). This is what makes a citation a *certificate*: the relationship is part of the
checked type. `describeA`/`describeC` name the roles in error messages, since upper and lower
evidence swap them. -/
def checkCertificateType (cert assumption conclusion : Name)
    (describeA : String := "the registered interface")
    (describeC : String := "the registered port statement") : CommandElabM Unit := do
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
        definitionally {describeA} '{assumption}' of the cited principle"
    unless ← Meta.isDefEq args[1]! (mkConst conclusion) do
      throwError "registry: certificate '{cert}' concludes '{args[1]!}', which is not \
        definitionally {describeC} '{conclusion}'"

/-- Check that `cert` has type `A ↔ C` (in either orientation) for the registered principle
interface and port statement — required for `exact`-direction relative evidence. -/
def checkIffCertificateType (cert assumption conclusion : Name) : CommandElabM Unit := do
  liftTermElabM do
    let info ← getConstInfo cert
    let ty ← Meta.whnfR info.type
    let fn := ty.getAppFn
    unless fn.isConstOf ``Iff do
      throwError "registry: exact-direction relativeProof evidence requires a certificate of \
        type '{assumption} ↔ {conclusion}'; '{cert}' has type '{ty}'"
    let args := ty.getAppArgs
    unless args.size == 2 do
      throwError "registry: unexpected arity in certificate type '{ty}'"
    let straight ← Meta.isDefEq args[0]! (mkConst assumption) <&&>
      Meta.isDefEq args[1]! (mkConst conclusion)
    let flipped ← Meta.isDefEq args[0]! (mkConst conclusion) <&&>
      Meta.isDefEq args[1]! (mkConst assumption)
    unless straight || flipped do
      throwError "registry: certificate '{cert}' is an Iff, but its sides are not \
        definitionally the registered interface '{assumption}' and port statement \
        '{conclusion}'"

/-- Look up a registered port by id. -/
def findPort? (env : Environment) (id : Name) : Option PortEntry :=
  (portExt.getState env).find? (·.id == id)

/-- The ambient a given evidence kind must live in. Kind and ambient must agree: a relative
factorization is ambient-Lean, a semantic implication lives in model semantics, a syntactic
derivation in an object theory. -/
def requiredAmbient : EvidenceKind → ProofAmbient
  | .dependencyAudit | .frontierSlice | .relativeProof => .lean
  | .fragmentCheck => .checkedFragment ⟨.anonymous⟩
  | .semanticImplication => .modelSemantics
  | .syntacticDerivation => .objectTheory

/-- Whether an ambient agrees with the required one (any fragment id matches
`checkedFragment`). -/
def ambientAgrees (required actual : ProofAmbient) : Bool :=
  match required, actual with
  | .checkedFragment _, .checkedFragment _ => true
  | r, a => r == a

/-- Validate one evidence record against the registry and the cited port statement.

Hardening invariants (each rejection is a hard error, never a silent downgrade):

* ambient-Lean evidence carries no RM semantic scope, and no scope is ever escalated;
* evidence kind and ambient must agree;
* `semanticImplication` requires an explicit scope;
* `backendChecked` is unregisterable while no backend exists;
* `kernelChecked` is accepted **only** for `relativeProof`, whose citation must be a typed,
  direction-aware certificate: `RelativeCertificate interface port` for `upper`,
  `RelativeCertificate port interface` for `lower`, and `interface ↔ port` for `exact`. Until
  typed schemas exist for semantic/syntactic evidence, kernel-checked citations of those kinds
  are rejected outright — an axiom audit alone (which `True.intro` passes) certifies nothing. -/
def validateEvidence (e : EvidenceRecord) (portDecl? : Option Name) : CommandElabM Unit := do
  if e.ambient == .lean && e.scope?.isSome then
    throwError "registry: ambient-Lean evidence carries no RM semantic scope; remove the \
      scope or change the ambient"
  unless ambientAgrees (requiredAmbient e.kind) e.ambient do
    throwError "registry: evidence kind '{repr e.kind}' requires ambient \
      '{repr (requiredAmbient e.kind)}', got '{repr e.ambient}'"
  if e.scope?.isSome && e.kind != .semanticImplication then
    throwError "registry: only semanticImplication evidence may carry a semantic scope"
  if e.kind == .semanticImplication && e.scope?.isNone then
    throwError "registry: semanticImplication evidence requires an explicit scope \
      (fullStandardModel | omegaModels | allModels); scope is never defaulted"
  if e.kind == .relativeProof && e.assumes?.isNone then
    throwError "registry: relativeProof evidence must name the assumed statement variant \
      (assumes ...), even when merely claimed"
  if e.assumes?.isSome && e.kind != .relativeProof then
    throwError "registry: only relativeProof evidence may carry assumes"
  if e.kind == .syntacticDerivation && e.theory?.isNone then
    throwError "registry: syntacticDerivation evidence must name its object theory \
      (theory ...), through the dedicated field rather than the scope"
  if e.theory?.isSome && e.kind != .syntacticDerivation then
    throwError "registry: only syntacticDerivation evidence may carry a theory"
  if e.thm?.isSome && e.verification != .kernelChecked then
    throwError "registry: via citations are only for kernelChecked evidence; cite literature \
      in the note"
  if e.verification == .backendChecked then
    throwError "registry: no backend exists yet; backendChecked evidence cannot be registered"
  if e.verification == .kernelChecked then
    unless e.kind == .relativeProof do
      throwError "registry: no typed certificate schema exists yet for kernel-checked \
        '{repr e.kind}' evidence; an axiom audit alone certifies nothing, so it is rejected \
        until a typed schema exists"
    let some thm := e.thm?
      | throwError "registry: relativeProof evidence must cite its certificate (via ...)"
    checkStandardAxioms thm
    let some assumes := e.assumes?
      | throwError "registry: relativeProof evidence must name the assumed statement \
        variant (assumes ...)"
    let cat := ConceptCatalog.ofEnv (← getEnv)
    unless cat.conflicts.isEmpty do
      let lines := "\n  ".intercalate cat.conflicts.toList
      throwError "registry: conceptual catalog is conflicted; resolve before registering \
        evidence:\n  {lines}"
    let some ventry := cat.findVariant? assumes.name
      | throwError "registry: unknown statement variant '{assumes.name}'"
    let some interface := ventry.interface?
      | throwError "registry: statement variant '{assumes.name}' has no Lean interface"
    let some portDecl := portDecl?
      | throwError "registry: relativeProof evidence requires the target variant to own a \
        Lean interface"
    match e.direction with
    | .upper => checkCertificateType thm interface portDecl
    | .lower =>
      checkCertificateType thm portDecl interface
        (describeA := "the registered port statement")
        (describeC := "the registered interface")
    | .exact => checkIffCertificateType thm interface portDecl

/-- The certified claims of a port, derived from its (already-validated) evidence. Only
kernel-checked `relativeProof` records produce claims today, and they are
`ambientFactorization`-scoped — never an RM bound. Claimed/literature evidence never produces a
claim, so a bogus lower literature record cannot suppress "exact lower bound: pending". -/
def PortEntry.certifiedClaims (p : PortEntry) : Array CertifiedClaim := Id.run do
  let mut claims := #[]
  let mut i := 0
  for e in p.evidence do
    if e.kind == .relativeProof && e.verification == .kernelChecked then
      claims :=
        claims.push { scope := .ambientFactorization, direction := e.direction, evidence := i }
    i := i + 1
  return claims

/-! ## Registration commands -/

/-- Resolve an identifier to a global constant. -/
private def resolveConst (id : TSyntax `ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

/-- One evidence line of a `revmath_port` command:
`evidence <kind> <direction> <verification> <ambient> [scope <s>] [theory <t>] [via <thm>]
[assumes <p>] [note "…"]`. -/
syntax rmEvidenceLine := &"evidence" ident ident ident ident (&"scope" ident)?
  (&"theory" ident)? (&"via" ident)? (&"assumes" ident)? (&"note" str)?

/-- `revmath_port id where mathlib := … target := … relation := … …`: register a port with
its evidence. The target is an exact statement variant; the port statement is **derived from
that variant's Lean interface**, so the two can never drift. All cited names must resolve;
kernel-checked citations are axiom-swept; typed certificates are matched against the assumed
variant's interface and the target's interface up to definitional equality. -/
syntax (name := revmathPortCmd) "revmath_port " ident " where "
  &"mathlib" " := " ident
  &"target" " := " ident
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
  let target : StatementVariantId := ⟨stx[8].getId⟩
  let cat0 := ConceptCatalog.ofEnv (← getEnv)
  let some ventry := cat0.findVariant? target.name
    | throwErrorAt stx[8] "registry: unknown statement variant '{target.name}'"
  let portDecl? := ventry.interface?
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
    let theory? : Option TheoryId := (optArg ev[6] 1).map fun s => ⟨s.getId⟩
    let thm? ← (optArg ev[7] 1).mapM fun s => resolveConst ⟨s⟩
    let assumes? : Option StatementVariantId := (optArg ev[8] 1).map fun s => ⟨s.getId⟩
    let evNote : String :=
      ((optArg ev[9] 1).map fun s => (⟨s⟩ : TSyntax `str).getString).getD ""
    let rec' : EvidenceRecord :=
      { kind, direction, verification, ambient, scope?, theory?, thm?, assumes?,
        note := evNote }
    validateEvidence rec' portDecl?
    evidence := evidence.push rec'
  if (findPort? (← getEnv) id).isSome then
    throwError "registry: duplicate port id '{id}'"
  modifyEnv fun env => portExt.addEntry env
    { id, mathlibDecl? := some mathlibDecl, target, portDecl?, relation,
      claimedClassical? := claimed?, note, evidence }

/-! ## Rendering (fail-closed) -/

/-- Render a certified claim scope. ω-model, all-model, and syntactic results render
separately; no scope is ever displayed as another. -/
def CertifiedClaimScope.render : CertifiedClaimScope → String
  | .ambientFactorization => "ambient Lean factorization"
  | .checkedFragment => "checked fragment membership"
  | .omegaModels => "all ω-models"
  | .allModels => "all models"
  | .syntacticDerivation t => s!"syntactic derivation in {t.name}"

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
  lines := lines.push s!"  target: {p.target.serialized}"
  lines := lines.push s!"  port: {(p.portDecl?.map toString).getD "none"}"
  lines := lines.push s!"  source relation: {p.relation.render}"
  for e in p.evidence do
    lines := lines ++ e.render
  match p.claimedClassical? with
  | some c => lines := lines.push s!"  candidate classical classification: {c} [claimed, UNVERIFIED]"
  | none => lines := lines.push s!"  candidate classical classification: unknown"
  let claims := p.certifiedClaims
  let rmClaims := claims.filter (·.scope.isRMBound)
  if rmClaims.isEmpty then
    lines := lines.push s!"  backend RM certificate: pending"
  else
    for c in rmClaims do
      lines := lines.push s!"  certified RM bound ({c.scope.render}, {c.direction.render})"
  unless rmClaims.any fun c => c.direction == .lower || c.direction == .exact do
    lines := lines.push s!"  exact lower bound: pending"
  unless p.note.isEmpty do
    lines := lines.push s!"  note: {p.note}"
  return "\n".intercalate lines.toList

/-- `#revmath_registry`: print every registered port, sorted by id (concepts and variants are
listed by `#rm_concepts`). -/
elab "#revmath_registry" : command => do
  let env ← getEnv
  let ports := (portExt.getState env).qsort fun a b => Name.lt a.id b.id
  let ql := ports.toList.map PortEntry.render
  logInfo <| "\n".intercalate ([s!"ports ({ports.size}):"] ++ ql)

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
  let cat := ConceptCatalog.ofEnv env
  let ports := portExt.getState env
  let evs := ports.flatMap (·.evidence)
  let count (v : Verification) := evs.filter (·.verification == v) |>.size
  let certified := (ports.flatMap (·.certifiedClaims)).filter (·.scope.isRMBound) |>.size
  logInfo <| s!"concepts: {cat.concepts.size}; variants: {cat.variants.size}; \
    ports: {ports.size}; evidence: {evs.size} \
    ({count .kernelChecked} kernel checked, {count .claimed} claimed, \
    {count .backendChecked} backend checked); certified RM bounds: {certified}"

end ReverseMathlib.Meta
