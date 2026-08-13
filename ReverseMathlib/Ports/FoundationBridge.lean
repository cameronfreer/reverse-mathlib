/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.BackendEvidence
import ReverseMathlib.Ports.Omega.HallEfilc

/-!
# Backend evidence: the reverse-mathlib-foundation ω-semantics bridge

Registers the `rmFoundationBridge` namespace with its four exact aliases and ingests
the bridge's versioned evidence file
(`imports/reverse-mathlib-foundation/rmlib-bridge-evidence.json`, copied verbatim from
the pinned bridge revision). The aliases resolve the backend's context key to the
registered semantic context and its variant keys to the exact Turing-ideal statement
variants — the backend's L₂ **sentences** are deliberately not aliased to anything: the
adapter theorems exist precisely because syntax and model-facing capability are
distinct artifacts.

What ingestion establishes, kept permanently distinct:

* **checked forward context realization** — every Turing ideal satisfies the backend's
  semantic RCA₀ theory (one-way; converse context adequacy still pending);
* **checked unconditional statement adapters** for ŴKL, EFILC, and one-sided Hall;
* **calculus identities and calculus-relative nonderivability** — `Rca0Theory ⊬
  wklSentence` in the backend's `henkinSafeV1` calculus AND in the backend's pinned
  standard calculus `l2VarWitnessLK.v1` (the fully specified LK presentation of the
  two-sorted logic assumed in Simpson §I.2, with logical equality, direct soundness
  against equality-correct structures, and the nonempty-sort and equality-rules
  assumptions as closed tags);
* **the typed calculus comparison** — both calculi independently sound; the record
  carries no embedding and licenses no derivability transfer;
* **the all-model semantic countermodel** — `Rca0Theory ⊭ wklSentence` over all
  general (Henkin-style) L₂ structures, witnessed by the ω-structure over REC.

Backend evidence never adds a local certified fact, graph edge, port, or closure
edge — but two fully validated records contribute checked scoped results to the
explicitly backend-qualified scoreboard columns: the semantic countermodel
(`all-model: 1 (backendChecked)`, qualifier `modelClass foundationStruc2General`)
and the standard-calculus nonderivability (`syntactic: 1 (backendChecked)`,
qualifier `calculus l2VarWitnessLK.v1` — the `henkinSafeV1` result never counts).
Any downgrade withdraws the contribution (the column falls back to 0). The local
certified-facts section stays exactly the local kernel-checked facts.
-/

namespace ReverseMathlib.Ports

rm_namespace rmFoundationBridge "cameronfreer/reverse-mathlib-foundation backend \
  evidence (rmlib-bridge-evidence/4): the external checked ω-semantics bridge to \
  FormalizedFormalLogic/Foundation — context-realization, statement-adapter, \
  calculus, calculus-comparison, and semantic-countermodel records ingested as \
  backend evidence, with interface fingerprints recomputed locally"

rm_external_ref rmFoundationBridge "rca0/turingIdealOmega" exactAlias semanticContext
  rca0.turingIdealOmega
rm_external_ref rmFoundationBridge "wkl/binaryTree.turingIdealOmega" exactAlias
  statement wkl.binaryTree.turingIdealOmega
rm_external_ref rmFoundationBridge
  "efilc/explicitSequential.enumeratedFibers.turingIdealOmega" exactAlias statement
  efilc.explicitSequential.enumeratedFibers.turingIdealOmega
rm_external_ref rmFoundationBridge
  "countableHall/oneSidedInjective.enumeratedCandidates.turingIdealOmega" exactAlias
  statement countableHall.oneSidedInjective.enumeratedCandidates.turingIdealOmega

/- The artifact-publishing revision: the bridge commit whose tree contains the vendored
artifact byte-for-byte. Necessarily distinct from the artifact's embedded export/check
revision (`ffcebe5…`) — by self-reference, the artifact cannot be committed at the
revision it records. Both are stored, exported, and rendered. -/
rm_ingest_bridge_evidence "imports/reverse-mathlib-foundation/rmlib-bridge-evidence.json"
  artifactRevision := "13b9b6b379712a63ba8c8bb9f6bcf9775adadf3b"

end ReverseMathlib.Ports
