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
* **calculus identity and calculus-relative nonderivability** — `Rca0Theory ⊬
  wklSentence` in the backend's `henkinSafeV1` calculus, standard-calculus comparison
  still pending.

No certified fact, no port, no closure edge, no graph edge, and no scoreboard change:
the certified counts remain exactly what `#revmath_stats` reports without this module.
-/

namespace ReverseMathlib.Ports

rm_namespace rmFoundationBridge "cameronfreer/reverse-mathlib-foundation backend \
  evidence (rmlib-bridge-evidence/1): the external checked ω-semantics bridge to \
  FormalizedFormalLogic/Foundation — context-realization, statement-adapter, and \
  calculus records ingested as backend evidence only, with interface fingerprints \
  recomputed locally"

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
revision (`39ec48b…`) — by self-reference, the artifact cannot be committed at the
revision it records. Both are stored, exported, and rendered. -/
rm_ingest_bridge_evidence "imports/reverse-mathlib-foundation/rmlib-bridge-evidence.json"
  artifactRevision := "ad99bc5bda3e5abfef6093ce32ae4c3032bea975"

end ReverseMathlib.Ports
