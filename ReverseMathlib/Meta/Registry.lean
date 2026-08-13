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
  (which `True.intro` would pass) is never a certificate. Kernel-checked
  `semanticImplication` records cite a `SemanticImplicationCertificate`/
  `SemanticEquivalenceCertificate` validated against a **registered semantic context** (exact
  base predicate, matching scope, layer-matched model-indexed endpoints — an ambient variant
  is never substituted for a model-indexed one). Kernel-checked citations of any *other* kind
  (syntactic, fragment, audit) are rejected outright until typed schemas exist for them.
  Kernel-checked citations are additionally swept by `collectAxioms` against the standard
  three axioms, and evidence kind must agree with its ambient.
* **Certified claims carry an explicit scope and report per scope** (`CertifiedClaimScope`):
  ambient factorization, checked-fragment membership, ω-models, all models, and syntactic
  derivation render separately, and no scope is ever escalated automatically — an
  all-ω-model theorem is a *certified ω-model implication*, never an unqualified subsystem
  bound; even an all-model semantic result stays distinct until an explicit
  soundness/completeness bridge upgrades it. The scoreboard reports
  ω-model/all-model/syntactic counts on separate lines — there is deliberately no single
  "certified RM bounds" number. Syntactic evidence will additionally record its proof
  **route** (provenance) separately from its surviving derivation **artifact** — a
  `Prop`-level derivation is computationally erased however obtained. Claimed/literature
  evidence never produces a claim, so it can never suppress a `pending` line. Everything
  else prints `pending`/`UNVERIFIED`, and unknown prints `unknown`.
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

universe u

/-- A typed **semantic implication certificate**: for every model satisfying the registered
base context, the assumed model-indexed statement implies the target one. Generic in the
model type — the ω realization and the all-model layer instantiate it with their own model
types; the registered `SemanticContextEntry` fixes `Base` (and, through its layer's interface
schema, `Model`), so an accidental quantification over the wrong model class cannot
register. -/
structure SemanticImplicationCertificate {Model : Sort u} (Base P Q : Model → Prop) :
    Prop where
  /-- The implication over every model of the base context. -/
  proof : ∀ M, Base M → P M → Q M

/-- A typed semantic **equivalence** certificate, for `exact`-direction semantic evidence. -/
structure SemanticEquivalenceCertificate {Model : Sort u} (Base P Q : Model → Prop) :
    Prop where
  /-- The equivalence over every model of the base context. -/
  proof : ∀ M, Base M → (P M ↔ Q M)

/-- A typed semantic **nonimplication (countermodel) certificate**: some model of the base
context satisfies the assumed statement and falsifies the target one. A nonimplication is
never the derived negation of a failed implication search — it is witnessed by an explicit
countermodel, and its scope honesty is the same as an implication's: the claim is exactly
about the registered model class, never a turnstile underivability statement. -/
structure SemanticNonimplicationCertificate {Model : Sort u} (Base P Q : Model → Prop) :
    Prop where
  /-- The countermodel: a model of the base context satisfying `P` and falsifying `Q`. -/
  countermodel : ∃ M, Base M ∧ P M ∧ ¬ Q M

/-- How a syntactic-derivation claim was obtained (provenance). Orthogonal to
`DerivationArtifact`: completeness-mediated and direct proofs establish the same
provability proposition — they differ in provenance and in what artifacts survive. -/
inductive SyntacticProofRoute where
  /-- A derivation constructed directly. -/
  | direct
  /-- Obtained through a formalized completeness theorem from a semantic certificate. -/
  | semanticCompleteness
  /-- Obtained through a certified fragment interpretation. -/
  | fragmentInterpretation
  /-- Imported from an external checked proof. -/
  | importedChecked
  deriving Inhabited, Repr, BEq

/-- Stable tag for a syntactic proof route. -/
def SyntacticProofRoute.tag : SyntacticProofRoute → String
  | .direct => "direct"
  | .semanticCompleteness => "semanticCompleteness"
  | .fragmentInterpretation => "fragmentInterpretation"
  | .importedChecked => "importedChecked"

/-- What derivation artifact survives. A derivation represented in `Prop` is computationally
erased **however obtained** — even a visibly constructed one; extraction requires a
derivation object in `Type`, or serialized derivation code plus a verified checker. -/
inductive DerivationArtifact where
  /-- Only the provability proposition; no inspectable derivation survives. -/
  | propositionOnly
  /-- An inspectable derivation object in `Type`. -/
  | derivationObject
  /-- Serialized derivation code plus a verified checker. -/
  | serializedCheckedCode
  deriving Inhabited, Repr, BEq

/-- Stable tag for a derivation artifact. -/
def DerivationArtifact.tag : DerivationArtifact → String
  | .propositionOnly => "propositionOnly"
  | .derivationObject => "derivationObject"
  | .serializedCheckedCode => "serializedCheckedCode"

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

/-- A **scoped RM claim**: any certified claim at ω-model, all-model, or syntactic scope.
Deliberately not called an "RM bound": the per-scope predicates below stay separate, and the
scoreboard reports each count on its own line — an ω-model implication is a genuine scoped
reverse-mathematical claim but **never** an unqualified subsystem upper bound. -/
def CertifiedClaimScope.isScopedRMClaim : CertifiedClaimScope → Bool
  | .omegaModels | .allModels | .syntacticDerivation _ => true
  | .ambientFactorization | .checkedFragment => false

/-- Supports exactly a certified ω-model implication (`⊨ω`). -/
def CertifiedClaimScope.supportsOmegaModelClaim : CertifiedClaimScope → Bool
  | .omegaModels => true
  | _ => false

/-- Supports exactly a certified all-model consequence (`⊨all`). -/
def CertifiedClaimScope.supportsAllModelConsequence : CertifiedClaimScope → Bool
  | .allModels => true
  | _ => false

/-- Supports exactly a syntactic subsystem upper bound (`⊢`). -/
def CertifiedClaimScope.supportsSyntacticUpperBound : CertifiedClaimScope → Bool
  | .syntacticDerivation _ => true
  | _ => false

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
  /-- For `semanticImplication` (only): the registered semantic context the certificate
  quantifies over — required for kernel-checked semantic evidence. -/
  context? : Option SemanticContextId := none
  /-- For `syntacticDerivation` (only): how provability was obtained. -/
  route? : Option SyntacticProofRoute := none
  /-- For `syntacticDerivation` (only): what derivation artifact survives. -/
  artifact? : Option DerivationArtifact := none
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
  /-- For `semanticImplication` (only): a cross-link to the typed fact this evidence
  supports, for proof/provenance display. The fact's own certification lives in the
  fact-evidence registry (#24); this link never inflates the fact-level headline. -/
  factLink? : Option FactId := none
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

/-- A certification linking a typed **fact** to a semantic certificate (issue #24). The
semantic certificate is fundamentally evidence for the fact, not for a port; base theory,
scope, direction, and endpoints are **derived from the fact** — never repeated freely.
The headline scoreboard counts unique certified facts by scope, so multiple ports can
never inflate it. -/
structure FactEvidenceEntry where
  /-- The certified fact. -/
  fact : FactId
  /-- The registered semantic context the certificate quantifies over. -/
  context : SemanticContextId
  /-- The typed certificate declaration. -/
  thm : Name
  /-- Free-text qualifier. -/
  note : String := ""
  deriving Inhabited, Repr, BEq

/-- A **checked scoped result** contributed by a validated external backend — the
generic registry surface for scope-qualified claims whose endpoints cannot be
typed locally (pin: reverse-mathlib cannot state Foundation's `Struc₂`
predicates, so a backend record is more honest than a local fact). Never a
certified fact, graph edge, port, or closure edge; counted only in the
explicitly verification-qualified scoped-results scoreboard. Deduplication is
by the semantic key `(kind, modelClass, theory, sentence)`, never by source
id. -/
structure ScopedResultEntry where
  /-- The semantic scope of the claim. -/
  scope : FactScope
  /-- How the claim was checked (`backendChecked` for backend contributions). -/
  verification : Verification
  /-- The claim kind (e.g. `semanticCountermodel`). -/
  kind : String
  /-- The closed model-class tag (e.g. `foundationStruc2General`). -/
  modelClass : String
  /-- The exact source-side theory identity. -/
  theory : String
  /-- The exact source-side sentence identity. -/
  sentence : String
  /-- Source provenance (backend record id) — display only, never the dedup key. -/
  sourceId : String
  deriving Inhabited, Repr, BEq

/-- The semantic dedup key. -/
def ScopedResultEntry.semanticKey (e : ScopedResultEntry) :
    String × String × String × String :=
  (e.kind, e.modelClass, e.theory, e.sentence)

initialize scopedResultExt : SimplePersistentEnvExtension ScopedResultEntry
    (Array ScopedResultEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.flatten
  }

/-- The scoped results at a scope, deduplicated by semantic key. -/
def scopedResultsAt (entries : Array ScopedResultEntry) (s : FactScope) :
    Array ScopedResultEntry := Id.run do
  let mut seen : Array (String × String × String × String) := #[]
  let mut out : Array ScopedResultEntry := #[]
  for e in entries do
    if e.scope == s && !seen.contains e.semanticKey then
      seen := seen.push e.semanticKey
      out := out.push e
  return out

initialize factEvidenceExt : SimplePersistentEnvExtension FactEvidenceEntry
    (Array FactEvidenceEntry) ←
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

/-- Whether a fact-scope (of a registered semantic context) matches an evidence semantic
scope. `provability` and `fullStandardModel` match nothing — neither is a certified model
class. -/
def contextScopeMatches : FactScope → SemanticScope → Bool
  | .omegaModels, .omegaModels => true
  | .allModels, .allModels => true
  | _, _ => false

/-- The typed certificate shape a semantic claim requires: one structure per claim form,
so a countermodel can never masquerade as an implication (or vice versa). -/
inductive SemanticCertShape where
  /-- `SemanticImplicationCertificate`. -/
  | implication
  /-- `SemanticEquivalenceCertificate` (sides may match flipped). -/
  | equivalence
  /-- `SemanticNonimplicationCertificate` (explicit countermodel; never flipped). -/
  | nonimplication
  deriving Repr, BEq

/-- Check that `cert` has the exact typed certificate shape for the claim form —
`SemanticImplicationCertificate base p q`, the equivalence form for `exact` evidence, or
the nonimplication (countermodel) form for separations — up to definitional equality in
all three predicate positions: the registered base-context predicate and the exact
assumed/target variant interfaces. The model type is argument 0 and is fixed by `base`
through defeq. Only the equivalence form may match with its sides flipped. -/
def checkSemanticCertificateType (cert base p q : Name) (shape : SemanticCertShape) :
    CommandElabM Unit := do
  liftTermElabM do
    let info ← getConstInfo cert
    let ty ← Meta.whnfR info.type
    let fn := ty.getAppFn
    let expected := match shape with
      | .implication => ``SemanticImplicationCertificate
      | .equivalence => ``SemanticEquivalenceCertificate
      | .nonimplication => ``SemanticNonimplicationCertificate
    unless fn.isConstOf expected do
      throwError "registry: '{cert}' does not have type '{expected} _ _ _' (found '{ty}'); \
        a kernel-checked semantic citation must be a typed semantic certificate of the \
        claim form's exact shape"
    let args := ty.getAppArgs
    unless args.size == 4 do
      throwError "registry: unexpected arity in certificate type '{ty}'"
    unless ← Meta.isDefEq args[1]! (mkConst base) do
      throwError "registry: semantic certificate '{cert}' quantifies over base context \
        '{args[1]!}', which is not definitionally the registered context predicate '{base}'"
    if shape == .equivalence then
      let straight ← Meta.isDefEq args[2]! (mkConst p) <&&> Meta.isDefEq args[3]! (mkConst q)
      let flipped ← Meta.isDefEq args[2]! (mkConst q) <&&> Meta.isDefEq args[3]! (mkConst p)
      unless straight || flipped do
        throwError "registry: semantic equivalence certificate '{cert}' does not relate the \
          assumed interface '{p}' and the target interface '{q}' definitionally"
    else
      unless ← Meta.isDefEq args[2]! (mkConst p) do
        throwError "registry: semantic certificate '{cert}' assumes '{args[2]!}', which is \
          not definitionally the required source interface '{p}'"
      unless ← Meta.isDefEq args[3]! (mkConst q) do
        throwError "registry: semantic certificate '{cert}' concludes '{args[3]!}', which is \
          not definitionally the required target interface '{q}'"

/-- Look up a registered port by id. -/
def findPort? (env : Environment) (id : Name) : Option PortEntry :=
  (portExt.getState env).find? (·.id == id)

/-- Validate a fact certification (issue #24). Everything is **derived from the fact**:
its theory context must match the registered semantic context's base and scope exactly
(never escalated); only singleton implication/equivalence/nonimplication facts are
certifiable — conjunctions, conservation, and uniform facts are rejected fail-closed
until their schemas exist; both endpoint variants must live at the context's layer and own
interfaces; and the cited certificate must have the exact typed shape for the fact's kind
(`SemanticImplicationCertificate Base P Q` for implication,
`SemanticEquivalenceCertificate` for equivalence, and the countermodel-witnessed
`SemanticNonimplicationCertificate` for nonimplication), axiom-swept. -/
def validateFactCertification (cat : ConceptCatalog) (fid : FactId)
    (ctxId : SemanticContextId) (thm : Name) : CommandElabM Unit := do
  let some f := cat.facts.find? (·.id == fid)
    | throwError "registry: unknown fact '{fid}'"
  let some ctx := cat.semanticContexts.find? (·.id == ctxId)
    | throwError "registry: unknown semantic context '{ctxId}'"
  let (base, scope) ← match f.context with
    | .theoryContext b s => pure (b, s)
    | .uniformContext _ => throwError "registry: uniform facts have no semantic-certificate \
        schema; only theory-context facts can be certified"
  unless base == ctx.base do
    throwError "registry: fact '{fid}' is over base theory '{base.name}', not the semantic \
      context's base '{ctx.base.name}'"
  unless scope == ctx.scope do
    throwError "registry: fact '{fid}' has scope '{scope.tag}', which is not the semantic \
      context's scope '{ctx.scope.tag}'; scopes are never escalated or defaulted"
  let (lhs, rhs, shape) ← match f.statement with
    | .implication l r => pure (l, r, SemanticCertShape.implication)
    | .equivalence l r => pure (l, r, SemanticCertShape.equivalence)
    | .nonImplication l r => pure (l, r, SemanticCertShape.nonimplication)
    | s => throwError "registry: no certificate schema exists for '{s.kindTag}' facts; only \
        singleton implication, equivalence, and nonimplication facts can be certified today"
  let #[pv] := lhs.variants
    | throwError "registry: conjunction certificates are rejected fail-closed until \
        conjunction semantics exists (the lhs of '{fid}' has {lhs.variants.size} conjuncts)"
  let #[qv] := rhs.variants
    | throwError "registry: conjunction certificates are rejected fail-closed until \
        conjunction semantics exists (the rhs of '{fid}' has {rhs.variants.size} conjuncts)"
  let some pe := cat.findVariant? pv.name
    | throwError "registry: unknown statement variant '{pv.name}'"
  let some qe := cat.findVariant? qv.name
    | throwError "registry: unknown statement variant '{qv.name}'"
  unless pe.layer == ctx.layer do
    throwError "registry: endpoint variant '{pv.name}' is at layer '{pe.layer.name}', not \
      the semantic context's layer '{ctx.layer.name}'; an ambient variant is never \
      substituted for a model-indexed one"
  unless qe.layer == ctx.layer do
    throwError "registry: endpoint variant '{qv.name}' is at layer '{qe.layer.name}', not \
      the semantic context's layer '{ctx.layer.name}'; an ambient variant is never \
      substituted for a model-indexed one"
  let some pIface := pe.interface?
    | throwError "registry: statement variant '{pv.name}' has no Lean interface"
  let some qIface := qe.interface?
    | throwError "registry: statement variant '{qv.name}' has no Lean interface"
  checkStandardAxioms thm
  checkSemanticCertificateType thm ctx.contextDecl pIface qIface shape

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
def validateEvidence (e : EvidenceRecord) (target : StatementVariantId)
    (portDecl? : Option Name) : CommandElabM Unit := do
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
  if e.context?.isSome && e.kind != .semanticImplication then
    throwError "registry: only semanticImplication evidence may carry a semantic context"
  if e.factLink?.isSome && e.kind != .semanticImplication then
    throwError "registry: only semanticImplication evidence may cross-link a fact"
  if let some fl := e.factLink? then
    -- The link stays display-only and never affects counts, but display metadata must not
    -- be able to lie: the fact's scope, base, endpoints, and orientation must all match.
    let cat := ConceptCatalog.ofEnv (← getEnv)
    let some f := cat.facts.find? (·.id == fl)
      | throwError "registry: evidence cross-links unknown fact '{fl}'"
    let (fbase, fscope) ← match f.context with
      | .theoryContext b s => pure (b, s)
      | .uniformContext _ =>
        throwError "registry: evidence cannot cross-link a uniform fact"
    if let some s := e.scope? then
      unless contextScopeMatches fscope s do
        throwError "registry: evidence scope does not match the scope \
          '{fscope.tag}' of cross-linked fact '{fl}'"
    if let some ctxId := e.context? then
      if let some ctx := cat.semanticContexts.find? (·.id == ctxId) then
        unless ctx.base == fbase do
          throwError "registry: evidence context base '{ctx.base.name}' does not match the \
            base '{fbase.name}' of cross-linked fact '{fl}'"
    let some assumes := e.assumes?
      | throwError "registry: fact-cross-linking evidence must name its assumed variant"
    let (l, r, isEquiv) ← match f.statement with
      | .implication l r => pure (l, r, false)
      | .equivalence l r => pure (l, r, true)
      | _ => throwError "registry: evidence can only cross-link implication or equivalence \
          facts"
    let #[lv] := l.variants
      | throwError "registry: cross-linked fact '{fl}' has conjunction endpoints"
    let #[rv] := r.variants
      | throwError "registry: cross-linked fact '{fl}' has conjunction endpoints"
    let ok :=
      if isEquiv then
        e.direction == .exact &&
          ((assumes == lv && target == rv) || (assumes == rv && target == lv))
      else
        match e.direction with
        | .upper => assumes == lv && target == rv
        | .lower => target == lv && assumes == rv
        | .exact => false
    unless ok do
      throwError "registry: evidence direction/endpoints do not match cross-linked fact \
        '{fl}' (an implication link must respect orientation; an equivalence link must be \
        exact-direction over the fact's endpoint pair)"
  if e.route?.isSome && e.kind != .syntacticDerivation then
    throwError "registry: only syntacticDerivation evidence may carry a proof route"
  if e.artifact?.isSome && e.kind != .syntacticDerivation then
    throwError "registry: only syntacticDerivation evidence may carry a derivation artifact"
  if (e.kind == .relativeProof || e.kind == .semanticImplication) && e.assumes?.isNone then
    let kindWord := if e.kind == .relativeProof then "relativeProof" else "semanticImplication"
    throwError "registry: {kindWord} evidence must name the assumed statement variant \
      (assumes ...), even when merely claimed"
  if e.assumes?.isSome && e.kind != .relativeProof && e.kind != .semanticImplication then
    throwError "registry: only relativeProof and semanticImplication evidence may carry \
      assumes"
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
    let cat := ConceptCatalog.ofEnv (← getEnv)
    unless cat.conflicts.isEmpty do
      let lines := "\n  ".intercalate cat.conflicts.toList
      throwError "registry: conceptual catalog is conflicted; resolve before registering \
        evidence:\n  {lines}"
    match e.kind with
    | .relativeProof =>
      let some thm := e.thm?
        | throwError "registry: relativeProof evidence must cite its certificate (via ...)"
      checkStandardAxioms thm
      let some assumes := e.assumes?
        | throwError "registry: relativeProof evidence must name the assumed statement \
          variant (assumes ...)"
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
    | .semanticImplication =>
      -- Exact validation: registered context, matching scope, layer-matched endpoints, and
      -- a typed certificate quantifying over every model of the exact context predicate.
      let some thm := e.thm?
        | throwError "registry: kernel-checked semanticImplication evidence must cite its \
          certificate (via ...)"
      checkStandardAxioms thm
      let some ctxId := e.context?
        | throwError "registry: kernel-checked semanticImplication evidence must name its \
          registered semantic context (context ...); a free-floating model quantification \
          certifies nothing"
      let some ctx := cat.semanticContexts.find? (·.id == ctxId)
        | throwError "registry: unknown semantic context '{ctxId}'"
      let some scope := e.scope?
        | throwError "registry: semanticImplication evidence requires an explicit scope"
      unless contextScopeMatches ctx.scope scope do
        throwError "registry: evidence scope '{repr scope}' does not match the registered \
          scope of semantic context '{ctxId}' ('{ctx.scope.tag}'); scopes are never \
          escalated or defaulted"
      let some assumes := e.assumes?
        | throwError "registry: semanticImplication evidence must name the assumed \
          statement variant (assumes ...)"
      let some aentry := cat.findVariant? assumes.name
        | throwError "registry: unknown statement variant '{assumes.name}'"
      let some tentry := cat.findVariant? target.name
        | throwError "registry: unknown statement variant '{target.name}'"
      unless aentry.layer == ctx.layer do
        throwError "registry: assumed variant '{assumes.name}' is at layer \
          '{aentry.layer.name}', not the semantic context's layer '{ctx.layer.name}'; an \
          ambient variant is never substituted for a model-indexed one"
      unless tentry.layer == ctx.layer do
        throwError "registry: target variant '{target.name}' is at layer \
          '{tentry.layer.name}', not the semantic context's layer '{ctx.layer.name}'; an \
          ambient variant is never substituted for a model-indexed one"
      let some pIface := aentry.interface?
        | throwError "registry: statement variant '{assumes.name}' has no Lean interface"
      let some qIface := tentry.interface?
        | throwError "registry: statement variant '{target.name}' has no Lean interface"
      match e.direction with
      | .upper => checkSemanticCertificateType thm ctx.contextDecl pIface qIface .implication
      | .lower => checkSemanticCertificateType thm ctx.contextDecl qIface pIface .implication
      | .exact => checkSemanticCertificateType thm ctx.contextDecl pIface qIface .equivalence
    | k =>
      throwError "registry: no typed certificate schema exists yet for kernel-checked \
        '{repr k}' evidence; an axiom audit alone certifies nothing, so it is rejected \
        until a typed schema exists"

/-- The certified claims of a port, derived from its (already-validated) evidence.
Kernel-checked `relativeProof` records produce `ambientFactorization` claims — never an RM
claim; kernel-checked `semanticImplication` records produce claims at exactly their validated
scope (`omegaModels` or `allModels`), never escalated. Claimed/literature evidence never
produces a claim, so a bogus lower literature record cannot suppress
"exact lower bound: pending". -/
def PortEntry.certifiedClaims (p : PortEntry) : Array CertifiedClaim := Id.run do
  let mut claims := #[]
  let mut i := 0
  for e in p.evidence do
    if e.verification == .kernelChecked then
      match e.kind, e.scope? with
      | .relativeProof, _ =>
        claims := claims.push
          { scope := .ambientFactorization, direction := e.direction, evidence := i }
      | .semanticImplication, some .omegaModels =>
        claims := claims.push { scope := .omegaModels, direction := e.direction, evidence := i }
      | .semanticImplication, some .allModels =>
        claims := claims.push { scope := .allModels, direction := e.direction, evidence := i }
      | _, _ => pure ()
    i := i + 1
  return claims

/-! ## Registration commands -/

/-- Resolve an identifier to a global constant. -/
private def resolveConst (id : TSyntax `ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

/-- One evidence line of a `revmath_port` command:
`evidence <kind> <direction> <verification> <ambient> [scope <s>] [context <c>] [theory <t>]
[route <r>] [artifact <a>] [via <thm>] [assumes <p>] [note "…"]`. -/
syntax rmEvidenceLine := &"evidence" ident ident ident ident (&"scope" ident)?
  (&"context" ident)? (&"theory" ident)? (&"route" ident)? (&"artifact" ident)?
  (&"via" ident)? (&"assumes" ident)? (&"fact" ident)? (&"note" str)?

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

private def parseRoute (stx : Syntax) : CommandElabM SyntacticProofRoute :=
  match stx.getId with
  | `direct => pure .direct
  | `semanticCompleteness => pure .semanticCompleteness
  | `fragmentInterpretation => pure .fragmentInterpretation
  | `importedChecked => pure .importedChecked
  | r => throwErrorAt stx "registry: unknown proof route '{r}' (expected direct | \
      semanticCompleteness | fragmentInterpretation | importedChecked)"

private def parseArtifact (stx : Syntax) : CommandElabM DerivationArtifact :=
  match stx.getId with
  | `propositionOnly => pure .propositionOnly
  | `derivationObject => pure .derivationObject
  | `serializedCheckedCode => pure .serializedCheckedCode
  | a => throwErrorAt stx "registry: unknown derivation artifact '{a}' (expected \
      propositionOnly | derivationObject | serializedCheckedCode)"

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
    let context? : Option SemanticContextId := (optArg ev[6] 1).map fun s => ⟨s.getId⟩
    let theory? : Option TheoryId := (optArg ev[7] 1).map fun s => ⟨s.getId⟩
    let route? ← (optArg ev[8] 1).mapM parseRoute
    let artifact? ← (optArg ev[9] 1).mapM parseArtifact
    let thm? ← (optArg ev[10] 1).mapM fun s => resolveConst ⟨s⟩
    let assumes? : Option StatementVariantId := (optArg ev[11] 1).map fun s => ⟨s.getId⟩
    let factLink? : Option FactId := (optArg ev[12] 1).map fun s => ⟨s.getId⟩
    let evNote : String :=
      ((optArg ev[13] 1).map fun s => (⟨s⟩ : TSyntax `str).getString).getD ""
    let rec' : EvidenceRecord :=
      { kind, direction, verification, ambient, scope?, context?, theory?, route?, artifact?,
        thm?, assumes?, factLink?, note := evNote }
    validateEvidence rec' target portDecl?
    evidence := evidence.push rec'
  if (findPort? (← getEnv) id).isSome then
    throwError "registry: duplicate port id '{id}'"
  modifyEnv fun env => portExt.addEntry env
    { id, mathlibDecl? := some mathlibDecl, target, portDecl?, relation,
      claimedClassical? := claimed?, note, evidence }

/-- `revmath_certify_fact id where context := c via := thm [note := "…"]`: certify a typed
fact against a registered semantic context (issue #24). Base theory, scope, direction, and
endpoints are derived from the fact; see `validateFactCertification` for the full matrix. -/
syntax (name := revmathCertifyFactCmd) "revmath_certify_fact " ident " where "
  &"context" " := " ident
  &"via" " := " ident
  (&"note" " := " str)? : command

@[command_elab revmathCertifyFactCmd]
def elabRevmathCertifyFact : CommandElab := fun stx => do
  let cat := ConceptCatalog.ofEnv (← getEnv)
  unless cat.conflicts.isEmpty do
    let lines := "\n  ".intercalate cat.conflicts.toList
    throwError "registry: conceptual catalog is conflicted; resolve before certifying \
      facts:\n  {lines}"
  let fid : FactId := ⟨stx[1].getId⟩
  let ctxId : SemanticContextId := ⟨stx[5].getId⟩
  let thm ← resolveConst ⟨stx[8]⟩
  let note : String :=
    ((optArg stx[9] 2).map fun s => (⟨s⟩ : TSyntax `str).getString).getD ""
  if (factEvidenceExt.getState (← getEnv)).any fun e => e.fact == fid && e.thm == thm then
    throwError "registry: fact '{fid}' is already certified via '{thm}'"
  validateFactCertification cat fid ctxId thm
  modifyEnv fun env => factEvidenceExt.addEntry env { fact := fid, context := ctxId, thm, note }

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
  if let some c := e.context? then
    lines := lines.push s!"    semantic context: {c}"
  if let some fl := e.factLink? then
    lines := lines.push s!"    supports fact: {fl}"
  if e.route?.isSome || e.artifact?.isSome then
    let route := (e.route?.map (·.tag)).getD "unrecorded"
    let artifact := (e.artifact?.map (·.tag)).getD "unrecorded"
    lines := lines.push s!"    route: {route}; artifact: {artifact}"
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
  let scopedClaims := claims.filter (·.scope.isScopedRMClaim)
  if scopedClaims.isEmpty then
    lines := lines.push s!"  backend RM certificate: pending"
  else
    for c in scopedClaims do
      let label := if c.scope.supportsSyntacticUpperBound then "certified syntactic RM bound"
        else
          let shape := if c.direction == .exact then "equivalence" else "implication"
          if c.scope.supportsAllModelConsequence then s!"certified all-model {shape}"
          else s!"certified ω-model {shape}"
      lines := lines.push s!"  {label} ({c.scope.render}, {c.direction.render})"
  unless scopedClaims.any fun c => c.direction == .lower || c.direction == .exact do
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

/-- The unique certified facts at a scope: distinct fact ids with at least one registered
certification, filtered by the fact's own scope. Multiple certificates — and any number of
port evidence records — never inflate this count (#24). -/
def certifiedFactsAt (cat : ConceptCatalog) (factEvs : Array FactEvidenceEntry)
    (s : FactScope) : Array FactEntry :=
  cat.facts.filter fun f =>
    (match f.context with
      | .theoryContext _ fs => fs == s
      | .uniformContext _ => false) &&
    factEvs.any (·.fact == f.id)

/-- `#revmath_facts`: the evidence-aware fact view (the catalog-data view is `#rm_facts`).
Certified facts render their certificates and the context-realization status — the
kernel-checked claim (over the registered context predicate) is never conflated with the
literature-backed identification of that predicate with the base theory's model class,
whose backend adequacy is pending. Uncertified facts stay "recorded, no evidence linked". -/
elab "#revmath_facts" : command => do
  let cat ← requireCleanCatalog
  let factEvs := factEvidenceExt.getState (← getEnv)
  let facts := cat.facts.qsort fun a b => toString a.id.name < toString b.id.name
  let mut lines := #[s!"facts ({facts.size}):"]
  for f in facts do
    let certs := factEvs.filter (·.fact == f.id)
    if certs.isEmpty then
      lines := lines.push
        s!"  {f.id.name} [{f.statement.kindTag} | {f.context.render}] \
          {f.statement.render} — recorded, no evidence linked"
    else
      lines := lines.push
        s!"  {f.id.name} [{f.statement.kindTag} | {f.context.render}] \
          {f.statement.render} — CERTIFIED"
      -- Per-certificate realization lines, data-driven: the kind word comes from the fact's
      -- statement, and the realization status is the registered context's own description —
      -- no universal status is manufactured here.
      let kindWord := match f.statement with
        | .implication .. => "implication"
        | .equivalence .. => "equivalence"
        | .nonImplication .. => "nonimplication (countermodel)"
        | _ => "fact"
      for c in certs do
        lines := lines.push s!"    via {c.thm} [context {c.context}]"
        unless c.note.isEmpty do
          lines := lines.push s!"      note: {c.note}"
        if let some ctx := cat.semanticContexts.find? (·.id == c.context) then
          lines := lines.push s!"      realization: {kindWord} kernel-checked over \
            '{ctx.contextDecl}'; context status: {ctx.description}"
  logInfo ("\n".intercalate lines.toList)

/-- `#revmath_stats`: the honest scoreboard — evidence counts by verification, and the
**unique certified facts per scope** (#24): distinct certified facts, so neither multiple
certificates nor multiple ports inflate the headline. Never a single undifferentiated
"certified RM bounds" number: an ω-model fact is reported as exactly that, not as a
subsystem bound. -/
elab "#revmath_stats" : command => do
  let env ← getEnv
  let cat := ConceptCatalog.ofEnv env
  let ports := portExt.getState env
  let factEvs := factEvidenceExt.getState env
  let evs := ports.flatMap (·.evidence)
  let count (v : Verification) := evs.filter (·.verification == v) |>.size
  let scopedRes := scopedResultExt.getState env
  -- one scoreboard cell: local certified facts (kernelChecked by construction)
  -- plus deduplicated scoped results, annotated by verification source
  let cell (s : FactScope) (facts : Nat) : String :=
    let contrib := scopedResultsAt scopedRes s
    let kc := facts + (contrib.filter (·.verification == .kernelChecked)).size
    let bc := (contrib.filter (·.verification == .backendChecked)).size
    let total := kc + bc
    if total == 0 then "0"
    else if bc == 0 then s!"{total} (kernelChecked)"
    else if kc == 0 then s!"{total} (backendChecked)"
    else s!"{total} ({kc} kernelChecked, {bc} backendChecked)"
  let omega := cell .omegaModels (certifiedFactsAt cat factEvs .omegaModels).size
  let allM := cell .allModels (certifiedFactsAt cat factEvs .allModels).size
  let syn := cell .provability (certifiedFactsAt cat factEvs .provability).size
  logInfo <| s!"concepts: {cat.concepts.size}; variants: {cat.variants.size}; \
    ports: {ports.size}; evidence: {evs.size} \
    ({count .kernelChecked} kernel checked, {count .claimed} claimed, \
    {count .backendChecked} backend checked); checked scoped results — \
    ω-model: {omega}; all-model: {allM}; syntactic: {syn}"

end ReverseMathlib.Meta
