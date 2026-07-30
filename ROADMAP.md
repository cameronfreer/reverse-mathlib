# Roadmap

Long-term direction for reverse-mathlib, deliberately kept out of the Milestone 1
implementation plan. The near-term work is tracked as GitHub issues (tranche 1 remainder and
tranche 2); everything after that lives here as ordered entries until the architecture has been
grown through concrete mathematical pressure — not designed as an encyclopedia in advance.

## Thesis

**Use Simpson as the vertical theorem spine, and RMZoo as the horizontal principle graph.**

Simpson ([Sim09], *Subsystems of Second Order Arithmetic*, 2nd ed.) tells us which
representations and reversals are mathematically canonical. RMZoo tells us that the eventual
registry must handle much more than a Big-Five ranking: conjunctions, implication and
non-implication, ω-model consequence, conservation, formula classes, and several notions of
uniform reducibility.

The long-term target:

> A typed, presentation-aware, proof-carrying superset of the RMZoo database, with
> import/export compatibility and Lean certificates where available.

```
Simpson theorem/citation ─────┐
                              │
RMZoo principle/fact ─────────┼──► typed catalog
                              │       │
mathlib theorem/proof ────────┘       ├──► literature claim
                                      ├──► ambient Lean factorization
                                      ├──► restricted replay
                                      ├──► ω-model certificate
                                      └──► syntactic backend certificate
                                              │
                                              ▼
                               RMZoo DSL / JSON / DOT / website
```

## RMZoo

RMZoo (<https://github.com/ericastor/rmzoo>, MIT) is already a specialized inference engine
over facts such as implication, non-implication, conservation, and several computable/Weihrauch
reducibilities; it supports conjunctions (`SRT22+COH`), distinguishes ordinary RCA₀ consequence
from ω-model consequence, and records direct versus inferred justifications
(<https://rmzoo.math.uconn.edu/documentation/>). At the RMZoo snapshot inspected for this
roadmap, the public diagrams say "last updated April 2018"
(<https://rmzoo.math.uconn.edu/diagrams/>); the exact upstream commit is recorded when the
importer is built (issue #7). Treat RMZoo as an important existing standard and bibliography,
not an actively maintained presentation.

What reverse-mathlib can add that RMZoo lacks: exact formal definitions of principles; distinct
statement variants and presentations (RMZoo's `KL` does not say *which* König's lemma — binary,
explicitly bounded, merely finitely branching, ω-model, ambient — and these differ in strength);
links to Lean declarations; evidence scope and strength; kernel-checked direct facts;
proof-producing inference; proof-mined source relationships; source hashes. The JSON exporter
(`databaseToJSON.py`) leaves principle definitions empty — a useful legacy interchange format,
not a sufficient semantic schema. RMZoo's contributing page explicitly welcomes transcription of
Simpson (its Simpson section in `results.txt` has only three active entries), so a pinned,
attributed importer plus a generated upstream PR is a direct contribution opportunity.

### RMZoo interface rules

- **Never import RMZoo facts as Lean axioms.** An imported line like
  `RT22+WKL w-|> ACA "Seetapun–Slaman"` becomes catalog data
  (`evidence := literature/imported`, `status := reported`, scope recorded) — never a theorem.
- **Direct and derived facts carry separate trust labels.** A checked graph inference over
  literature-only leaves is `derived-from-literature`, not certified; only when every leaf has a
  Lean/backend certificate is the result fully certified.
- **Stable identity never depends on RMZoo's generated numeric UID.** Identity is layered —
  the concept-vs-variant distinction is itself part of the ID scheme: a *concept* id like
  `reverse-mathlib:wkl` has no privileged Lean proposition; *statement-variant* ids like
  `reverse-mathlib:wkl.binaryTree.ambient` / `.omegaModel` / `.secondOrderSyntax` may own an
  exact Lean interface; *uniform-problem* ids like
  `reverse-mathlib:wkl.binaryPathChoice.cantorRepresentation` identify represented problems.
  External references (`rmzoo:RT22`, `simpson:I.10.3`, `concordance:C017`) are **typed**: each
  carries a target and a relation (exact alias | source location | imported correspondence |
  related variant), and only exact aliases participate in identity resolution. Namespaces are
  registered, never a hard-coded allowlist.
- **Display choices stay display choices.** RMZoo's "is primary" designation is layout, not
  mathematics; store it separately from equivalence facts.
- **Upstreaming is a generated artifact**: pin a snapshot → import direct facts → add exact
  internal Simpson records → generate a candidate `simpson-2009-results.txt` → diff against
  upstream → coordinate conventions with maintainers → submit a focused PR. The legacy export
  stays conservative; rich definitions/evidence live in reverse-mathlib's JSON.

## Treatment axes and the concordance workbook

A curated concordance workbook (`reverse_mathematics_concordance.xlsx`, local at
`/home/freer/books/`; to be vendored with a content hash when the catalog seed lands) compares
121 variant-fixed rows across **five treatment axes**, and the catalog schema should reflect
all of them:

1. **Simpson / second-order RM** — subsystem equivalences and coding practice;
2. **Kohlenbach / proof mining** — extracted bounds, metastability, proof dependence (the
   Q-track);
3. **Sanders / higher-order RM** — RCA₀^ω and ECF conservation, the "Bigger Five", and the
   coding-gap principles;
4. **RMZoo** — the below-ACA implication/non-implication graph;
5. **Weihrauch** — uniform input→output problems and their degrees.

Rules the workbook gets right and the catalog must enforce:

- **One result variant / output problem per row; extend by adding a row, never by merging
  formulations** — exactly the statement-variant discipline (issue #4). The workbook even
  splits extreme value into "compute only max f" vs "choose an argmax point".
- **A subsystem equivalence never determines a Weihrauch degree.** Degree claims carry their
  own status: `Exact` / `Representative` (standard analogue, not a theorem-equivalence claim) /
  `Variant-sensitive` (representation, promise, output, or sequentialization must be fixed
  first) / `Not assigned`. "ACA₀ is a theory, not one Weihrauch degree."
- **A theorem provable in RCA₀ can still define a noncomputable uniform selector** if its
  classical premise is not decidable — base-provability is not uniform computability.
- The uniform-decomposition caution: RT²₂ ↔ SRT²₂+COH over RCA₀, but **RT²₂ is not
  Weihrauch-equivalent to SRT²₂ × COH** — second-order equivalences must never silently imply
  uniform facts (bears directly on tranche 5, item 36).
- Per-row **confidence** and **source keys** (SIM/KOH/SAN/RMZ/WH-\*) with URLs — the evidence
  and provenance model (issues #6, #10) should carry both.

The workbook has 51 rows pre-mapped to RMZoo symbols (a ready alias table for issue #7) and is
the primary literature seed for the catalog (issue #10) — richer than a Simpson-only
transcription, since each row already fixes the variant and cites all five axes. It has no
Hall/marriage row: the walking slice's matching ladder is complementary content we bring.

Seeding discipline: the workbook is a **research concordance and issue-seeding source, not
importable evidence**. It seeds candidate records and review queues; every exact mathematical
claim must be checked against its primary source before any status above claimed/UNVERIFIED;
"Representative"/"expected"/medium-confidence entries stay editorial notes; current manuscripts
and recent preprints are pinned by version/date; a `concordance:Cnnn` row ID is external
provenance, never canonical principle identity and never certification. Simpson references
should carry both the summary theorem list and the substantive development (e.g. II.8/IV.3 for
completeness, not only the I.x entry points).

### The uniformity axis, and variants vs uniform problems

Framed as four architectural axes: **Simpson** (nonuniform theorem strength and reversals),
**RMZoo** (horizontal implications/separations), **Kohlenbach** (extracted terms, bounds,
rates, moduli, metastability), and **higher-order RM / Weihrauch** (representation,
uniformization, exact computational strength). The workbook's Sanders rows show how innocent
changes move strength: coded vs arbitrary higher-type open sets; countable-as-injection vs
explicit enumeration; sequential vs ε–δ continuity; sequences vs arbitrary nets; countable vs
enumerable sets; coded gauges vs unrestricted functionals.

Schema consequence (amends issue #4): `StatementVariant` and **`UniformProblem`** are separate
objects — a theorem variant may be RCA₀-provable while uniformly *selecting* its witness is a
noncomputable choice problem (IVT existence vs zero-selection; maximum value vs argmax;
point-producing vs contrapositive Baire category; one-step vs full Hahn–Banach). A
`UniformProblem` carries input/output types, instance/solution predicates, and input/output
representations; a `uniformizes : StatementVariant → UniformProblem → Prop` relationship links
them. Weihrauch degrees attach to precisely represented uniform problems, never to theorem
nodes. Sequentialization/parallelization are explicit problem operations
(`ProblemOp.single | finiteParallelization | sequentialization` — metadata first, reduction
rules later): one instance and a sequence of instances differ, because sequentialization
introduces countable-choice or bar-recursive content.

Status semantics (amends issues #5/#6): `Exact` may become a typed reducibility/equivalence
claim with evidence; `Representative` is a descriptive comparison only — never an inference
edge; `Variant-sensitive` is a review marker meaning the problem is not yet specified enough;
`Not assigned` is absence of classification, not evidence of computability or weakness.
Workbook `Confidence` is editorial workflow metadata and never affects trust or certification
status. No inference rule crosses from RM implication to Weihrauch reducibility without a
registered bridge theorem; reducibility facts relate exact uniform-problem variants, not
acronym-level principles; nonuniform implication and uniform reducibility are different fact
families.

### What "subsuming RMZoo" could realistically mean

1. **Compatibility**: read and write its facts.
2. **Data-model subsumption**: every RMZoo relation plus exact variants and evidence.
3. **Inference subsumption**: reproduce its queries and diagrams with checked derivation
   objects.
4. **Content certification**: progressively replace literature-only leaves with Lean/backend
   certificates.

Levels 1–3 are achievable relatively early; level 4 is a decades-scale program (especially
non-implications, conservation, uniform reducibilities). Initially the project is a certified
backend and interoperable extension — not a replacement for RMZoo's community-maintained
knowledge.

## The theorem-family ladders (from [Sim09])

| Domain | Base/RCA₀ | WKL₀ | ACA₀ | ATR₀ / Π¹₁-CA₀ |
|---|---|---|---|---|
| Matching | finite Hall | 2-regular countable perfect matching (X.3.16) | locally finite Hall ↔ perfect matching (X.3.15) | countable König covering ↔ ATR₀ (X.3.12) |
| Analysis | IVT | Heine–Borel, Heine–Cantor, maximum principle | monotone convergence/LUB, Bolzano–Weierstrass | perfect-set and Cantor–Bendixson results |
| Logic | a restricted completeness formulation (I.8.3) | ordinary countable completeness (I.10.3) | — | determinacy-related principles |
| Algebra | existence of algebraic closures; existence and uniqueness of real closures for countable ordered fields | uniqueness of algebraic closures; prime ideals; real closures/orderings for countable formally real fields | maximal ideals, vector-space bases, transcendence bases | Abelian-group classification |
| WQO | elementary coding | — | Higman (X.3.22) | minimal bad sequences (X.3.24), Nash–Williams (X.3.29–30) |

Intermediate and non-Big-Five systems do not fit this table. In particular, WWKL₀ lies strictly
between RCA₀ and WKL₀ and will be represented in the horizontal principle graph, not forced
into a Big-Five column.

The **matching ladder stays first**: X.3.16 (WKL₀ ↔ 2-regular perfect matching), X.3.15 (ACA₀ ↔
locally finite Hall/perfect matching), X.3.12 (ATR₀ ↔ König covering) — one domain spanning
three systems, continuing the Hall walking slice. Important correction recorded from this
comparison: mathlib's countable Hall (and our `Standard.CountableHall`) is a **one-sided
injective-choice statement**; Simpson's X.3.15/X.3.16 concern perfect matchings saturating both
sides with Hall's condition on finite subsets of the whole bipartite vertex set — related
statement variants, **not identical**. The port record must say so.

The **analysis ladder** is the best second major domain (coded vs ambient reals, supplied vs
constructed moduli/LUBs/subsequences). **Completeness** is the best presentation-sensitivity
benchmark: Simpson I.8.3 has "a version" in RCA₀ while I.10.3 lists countable Gödel
completeness as WKL₀-equivalent — a single registry node `Completeness` would erase the
phenomenon; it must be a family of exact variants (second proof-mining experiment after Hall,
compared with constructive analyses such as MeReMath). **WQO theory** (X.3.20–X.3.24,
X.3.29–30; mathlib has Dickson/Higman in `Mathlib/Order/WellFoundedSet.lean` and
Cantor–Bendixson material in `Mathlib/Topology/Perfect.lean`) is a good later mining target
precisely because it does not form a Big-Five chain — Dickson's lemma forces the ontology to
represent well-ordering principles (WO(ω^ω)). Modern status of book-era conjectures (exact
Nash–Williams calibration) must be re-researched before opening formalization issues.

## Tranches

Tranche 1 items 1–4 are **complete** (dependency miner; Standard EFILC + countable Hall;
relative Hall proof; artifact-shaped registry). Items in *tranche 1 remainder* and *tranche 2*
are open GitHub issues; later tranches are ordered entries only.

### Tranche 1 remainder — finish the Hall walking slice
5. Binary/bounded/finitely-branching tree distinctions and EFILC bridges — **minimal, readable,
   ambient-Lean surface**, distinct from tranche 3's coding layer. Representation contract:
   `BinaryTree := Set (List Bool)`; `BoundedTree := Set (List ℕ)` + supplied coordinate bounds;
   `FinitelyBranchingTree := Set (List ℕ)` + a finite-successor proposition. Ordinary finite
   lists at the mathematical surface; encoding into naturals only inside the EFILC bridge where
   needed (this avoids prematurely blessing mathlib's `Encodable` representation as the
   eventual RCA₀ coding). Paths: binary ambient path = `Set ℕ` interpreted as positions
   containing 1; natural-valued ambient path = an ordinary function or bundled sequence; future
   ω-model path = an internal graph set with totality and single-valuedness proofs.
6. Classical wrappers, `countableHall_nat`, honest case-study report (including the Simpson
   X.3.15/X.3.16 variant relationship in the port record).
6a. Registry hardening: typed, direction-aware, scope-preserving certificates (see the
   Milestone 1 issue) — semantic/syntactic citations must not pass on an axiom audit alone;
   `RelativeCertificate P T` is an upper certificate only, lower requires `T → P`, exact
   requires `P ↔ T`; certified claims carry an explicit scope
   (`ambientFactorization | checkedFragment | omegaModels | allModels | syntacticDerivation`)
   and no scope is ever escalated automatically.

Registry future-proofing constraint: identifiers, evidence kinds, contexts, and external
mappings must be extensible. No RMZoo importer inside Milestone 1.

### Tranche 2 — the catalog/RMZoo seam
7. Conceptual principle identity (`PrincipleId`, aliases, external IDs, display metadata; a
   principle is not yet a Lean proposition).
8. Statement variants (`StatementVariant`, presentation requirements, semantic layer, optional
   Lean declaration — e.g. `WKL.binaryTree.standard` / `.omegaModel` / `.secondOrderSyntax`,
   `KL.explicitlyBounded.standard`, `KL.locallyFinite.omegaModel`).
9. Typed facts and contexts (implication/equivalence, non-implication, conservation,
   reducibility and non-reducibility, formula-class facts, normalized conjunctions — `RT22+COH`
   is an AST, not a magic string — base theory and semantic scope).
10. Evidence and provenance taxonomy (literature citation, imported RMZoo assertion, derived
    catalog fact, ambient Lean theorem, restricted replay, ω-model theorem, all-model semantic
    theorem, syntactic derivation, reversal, countermodel).
11. Pinned RMZoo import (vendor `results.txt` at an exact commit with MIT attribution; direct
    assertions only; everything `literature/imported`, never Lean-certified).
12. Proof-producing catalog inference (checked derivation calculus: transitivity, equivalence
    expansion, conjunction intro/elim, reducibility weakening, context weakening, supported
    conservation rules — certifies inferences, not citation leaves).
13. RMZoo-compatible export and query (legacy `results.txt` where representable, rich JSON,
    DOT/Graphviz, `#rm_query`, derivation explanations).
14. Literature catalog seed from the concordance workbook (121 variant-fixed rows citing
    Simpson/Kohlenbach/Sanders/RMZoo/Weihrauch with confidence and URLs; vendored with a
    content hash), subsuming the original Simpson-only seed (I.8.3, I.9.3, I.9.4, I.10.3,
    I.11.5, Appendix X) — all literature records with exact references and statement-variant
    placeholders.

### Tranche 3 — coding, trees, and matching vocabulary
15. Pairing / finite-sequence / finite-set codes (single vocabulary reused everywhere).
16. Internal function and enumeration graphs (internal graph sets vs arbitrary Lean functions
    vs program codes).
17. Canonical numeric and internal adapters for the Standard tree presentations (number
    codings, internal graph/set presentations, at-most-two-successor on arbitrary labels;
    migration of the tranche-1 list-based surface into the coding layer).
18. Bipartite graph and matching presentation matrix (one-sided injective choice; left/right
    saturating; perfect; local finiteness with explicit neighborhood enumeration; n-regularity;
    König covering).
19. Migrate the WKL/EFILC factorizations into typed `StatementVariant` facts (the ambient
    equivalence is proved in tranche 1; this item catalogs it, not re-proves it).
20. Map the current Hall port (implication/adaptation records among mathlib's Hall,
    `CountableHall`, left-saturating matchings, Simpson's perfect-matching variants).
21. Relative matching forward proofs (WKL/EFILC ⇒ regular-graph matching; ACA/range-search ⇒
    locally finite perfect matching — correctly labeled capability-level evidence).

### Tranche 4 — ω-model semantics and first exact calibrations
22. Turing-reducibility adapters and join (reuse `Mathlib/Computability`).
23. Turing jump (needed to characterize ACA₀ ω-models).
24. Second-order parts and internal sets (`OmegaPart`, internal pairs/graphs/functions/
    sequences/trees/paths).
25. Turing ideals / RCAω (closure conditions, basic examples; scope label `omegaModel` only).
26. WKLω and ACAω (path closure for internal infinite binary trees; relative
    jump/arithmetical-definability closure).
27. ACAω ↔ internal range existence (functions represented by internal graphs — quantifying
    over arbitrary Lean ℕ → ℕ would be wrong).
28. WKLω ↔ relative Σ⁰₁ separation (explicit relative-computability parameters).
29. WKLω ↔ EFILCω (re-run the standard proof over internal systems and section graphs).
30. Matching calibrations: ω-model forms of X.3.16 (WKLω ↔ 2-regular perfect matching) and
    X.3.15 (ACAω ↔ locally finite Hall/perfect matching).
31. Evidence matrix report per Hall/matching statement (literature / ambient / ω-model /
    all-model / syntactic / reversal status). Still no "formalized over RCA₀" claims without
    the all-model/object-theory backend.

### Tranche 5 — first genuinely non-Big-Five slice
32. Instance/solution problem abstraction (∀X (Instance X → ∃Y Solution X Y)) for computable
    and Weihrauch reductions.
33. RT²₂, SRT²₂, COH statements (exact coded and ω-model variants).
34. RT²₂ → SRT²₂ and RT²₂ → COH (Lean-backed replacements for imported RMZoo facts).
35. SRT²₂ + COH → RT²₂ (first substantive compound-antecedent catalog result).
36. Upgrade the RMZoo equivalence evidence for RT22 ↔ SRT22+COH (Cholak–Jockusch–Slaman /
    Mileti citations + exact variants + scope). Caution from the concordance: RT²₂ is **not**
    Weihrauch-equivalent to SRT²₂ × COH — the catalog must keep the second-order equivalence
    and the failed uniform decomposition as distinct facts on distinct axes.
37. WWKL and DNR statement families (without committing to the harder separations).
38. First uniform reduction pilot (one known constructive reduction, after a feasibility
    spike; validates the reducibility API).
39. Countermodel/non-implication certificate interface (explicit model/ω-model witness; never
    "failed to prove" as non-implication).

### Tranche 6 — the analysis ladder
40. Fast Cauchy real codes and correctness map to ℝ. 41. Coded real sequences. 42. Coded
continuous functions and moduli. 43. IVT in the RCA interface. 44. Heine–Borel from WKL.
45. WKL from Heine–Borel. 46. Heine–Cantor/boundedness/maximum principle from compactness —
with the maximum principle **split into two variants** (existence/computation of the maximum
*value* vs production of a maximizing *point*; different uniform content per the concordance).
47. Reversals for selected WKL function principles. 48. Bounded monotone ⇒ coded LUB from ACA.
49. ACA from monotone convergence/LUB. 50. Bolzano–Weierstrass from ACA. 51. ACA from
Bolzano–Weierstrass. 52. Mathlib port comparison (`CompactSpace.uniformContinuous_of_continuous`,
`tendsto_atTop_isLUB`, `tendsto_subseq_of_bounded` — identifying which strong construction the
generic theorem receives as a structure or hypothesis).

### Tranche 7 — logic and algebra
53. First-order syntax/proof-system adapter. 54. Completeness formulation matrix. 55. Mine an
existing Lean/Foundation completeness proof. 56. RCA-level restricted completeness. 57.
WKL-level countable completeness. 58. Countable ring and ideal codes. 59. Prime ideal theorem
from WKL and reversal. 60. Maximal ideal theorem from ACA and reversal. 61. Countable
vector-space basis from ACA and reversal. 62. Field closure ladder (existence of algebraic
closure in RCA₀; existence *and uniqueness* of real closure for countable ordered fields in
RCA₀; **uniqueness of algebraic closure** in WKL₀, alongside orderings/real closures of
countable formally real fields; transcendence basis in ACA₀ — cf. concordance C053–C057).

### Tranche 8 — WQO, ATR, and Π¹₁-CA
63. Adapters to mathlib's WQO/Higman API. 64. Dickson's lemma ↔ WO(ω^ω) (X.3.20). 65. Hilbert
basis theorem ↔ WO(ω^ω) (X.3.21). 66. Higman ↔ ACA (X.3.22). 67. Countable well-order codes.
68. ATR capability and transfinite recursion. 69. Comparability of countable well-orders ↔ ATR.
70. Countable König covering ↔ ATR (X.3.12 — the natural final chapter of the Hall/matching
sequence). Then horizon issues forcing serious backend work: 71. Borel and analytic codes.
72. Lusin separation/perfect-set theorem ↔ ATR. 73. Perfect-kernel construction.
74. Cantor–Bendixson ↔ Π¹₁-CA. 75. Minimal bad sequence lemma ↔ Π¹₁-CA (X.3.24).

### Later non-Big-Five domains
- **WWKL and measure**: X.1.9, X.1.13, X.1.14 (countable additivity, Vitali covering,
  measure-theoretic monotone convergence).
- **Banach-space calibration**: X.2.1 (WKL-equivalent separation), X.2.9 (Π¹₁-CA-equivalent
  weak-* closure existence). Mathematically excellent, representation-heavy.
- **Sanders' higher-order divergence family** ([San], via the concordance): NIN[0,1]/NBI[0,1]
  ("Bigger Five" — no injection/bijection [0,1]→ℕ, not provable from the Big Five), countable
  vs enumerable sets, the `open` coding principle ("every third-order open set has an RM-code"
  — it *isolates the logical cost of Simpson's coding practice*, a direct formalization of
  this project's presentation-sensitivity thesis), BOOT ↔ convergence of nets, Jordan
  decomposition for bounded variation, unordered sums, PHP[0,1]. These need the higher-order
  ambient (`RCA₀^ω`, ECF conservation — conservative over RCA₀ *only for second-order
  sentences*) and are horizon work, but the catalog schema must not preclude them: statement
  variants already carry a semantic layer, and `ProofAmbient`/`SemanticScope` extend.
- **Weihrauch axis**: uniform input→output degrees (Brattka–Gherardi and successors; e.g.
  BWT_ℝ ≡ jump of WKL, IVT ≡ CC₁, WKL ≡ C_{2^ℕ}). Enters the catalog as its own fact/evidence
  axis with the Exact/Representative/Variant-sensitive/Not-assigned status discipline — never
  inferred from subsystem equivalences.
- **Baire category as a schema stress test** (calibration family near the completeness matrix):
  coded point-producing form, contrapositive/index-output form, and arbitrary higher-order
  open-set form occupy strikingly different computational/foundational positions while all
  sounding like "the Baire category theorem".
- **Weak Bolzano–Weierstrass / strong cohesiveness bridge**: the concordance connects weak BW
  (Cauchy subsequence without a rate) with StCOH — a later benchmark tying together analysis,
  COH/StCOH combinatorics, quantitative/metastable formulations, and uniform computation. Add
  StCOH alongside COH when tranche 5 lands.
- **Later benchmark ladders** (roadmap families, not issues yet): Hahn–Banach (full
  infinite-dimensional / finite-dimensional / one-step extension); fixed points (dimension one /
  fixed dimension ≥ 2 / compact infinite-dimensional); ODEs (Banach contraction and
  Picard–Lindelöf vs Peano existence); Baire category (above); compactness (single instance vs
  sequentialized).

## Strict reverse mathematics (cross-cutting, not a sixth axis)

Friedman's strict RM enters as a **presentation-and-interpretation discipline** cutting across
the existing axes, under the design north star: *every classified object is a theorem realized
under a presentation, with supplied data, a proof route, an output effect, and evidence at a
declared semantic scope*. Presentation is mathematical data, and changing presentation can
consume logical, computational, or formalization strength.

Key correction, recorded so it is never re-introduced: **Friedman's P1 is not a presentation
of binary-tree WKL.** P1 is the halving-closed-set principle — a *distinct principle*
connected to WKL by a contextual equivalence fact. List-based trees vs numeric tree codes vs
internal graph sets *are* presentation relations; P1 vs tree-WKL is not (Friedman's ETF
manuscript, pinned by version/date when seeded, makes both distinctions explicit).

Design decisions (from review):
- Presentations become **reusable objects** (`PresentationId`/`PresentationEntry`) referenced
  by exact statement variants, with **evidence-bearing translation relations carrying semantic
  scope** — a second certificate family beside the reverse-mathematical one; uncertified
  translations are fail-closed and never enter implication closure. Do **not** commit to a
  separate `Realization` node up-front: test whether variant + presentation suffices, adding
  `Realization` only if the tree pilot exposes real duplication.
- The relation taxonomy is **not one enum**: literal / faithfulCoding / quotientPresentation
  concern *representations*; definitionalExtension / interpretation /
  arithmeticPreservingSynonymy concern *theories*; chosenRepresentatives is a construction
  effect or requirement.
- Strictness is **attributed evidence, never a Boolean**: `StrictnessAssessment` per dimension
  (base/statement/principle naturalness, no-code, literal object identity, interpretation
  distance) with statuses `assertedBy | arguedBy | contestedBy | editorialAssessment` —
  Friedman says "strictly mathematical" is not a sharp boundary, and the catalog must not
  manufacture consensus (`literatureAccepted` deliberately rejected). Lean certifies
  translations and reversals; it never settles naturalness by syntax.
- A strict incident is a package: base realization + target system/principle + theorem
  realization + equivalence fact + attributed assessments.
- Sequence: presentations/translations (issue) → ETF/FSRA/P1–P4 literature seed with exact
  base/system notation and claimed scopes (issue) → tree-presentation pilot → strict WKL and
  strict Hall pilots → the **deferred** ETF/FSRA syntax/semantics/synonymy backend (proving
  P1's calibration waits for a model/syntactic backend — defining ETF structures in
  unrestricted Lean and proving ambient theorems would not establish ETF strength, for the
  same reason ambient implications are not RCA₀ results).

## Reverse mathematics qua Lean, and the mining track

The three kernel axioms are too coarse an axis: `Classical.choice` conflates selection
strengths (and yields EM), `propext`/`Quot.sound` are not comprehension strengths, and a
proof-only audit ignores strength supplied *in the statement*. Every theorem eventually gets
three profiles: **statement burden** (`Finite` vs `Fintype`, `Countable` vs `Encodable`,
supplied moduli/bounds/codes, quotient vs representative), **proof-route burden** (the
frontier interfaces the proof traverses), and **witness/effect burden** (`Prop`-only vs
data-live output; a `Prop`-only classical argument is computationally erased but *not*
proof-theoretically free). Four assertion levels, extending the documented gate-certification
levels: occurrence → factorization → restricted replay → necessity/lower bound.

The **empirical Lean capability basis v0** (mine proof-only closures across a corpus, find
co-occurring frontier sets and dominators, collapse aliases, validate by hand-written
factorization and restricted replay — a capability *zoo*, not a designed "Lean Big Five")
comes only after Q6, route analysis, restricted replay, and at least three theorem families.
The capability lattice vocabulary (logic / selection / presentation / extensionality-quotient /
search-recursion / compactness-maximality / size-universe / computation-trust) is good
vocabulary that must emerge from evidence, not become a speculative enum.

Mining-track items (issues open only as their prerequisites land):
- **Route analysis** (near-term, independent): `#rm_paths`, `#rm_dominators`, representative
  path explanations, exact type-vs-proof-edge handling, fail-closed under truncation; minimum
  cuts as a stretch and only *relative to registered frontier families* (unconstrained cuts
  return trivial immediate dependencies). Every result is "architecture of the current
  elaborated proof; not logical necessity or an RM lower bound."
- **Restricted replay MVP** (after #6): sandbox module with approved imports/capability
  interfaces, replaying an already-explicit relative theorem (the Hall/EFILC slice as first
  fixture); fails on unapproved constants; records environment, source hash, allowed
  interface; renders `restrictedReplay`, never a lower bound. More valuable than mechanical
  slicing initially.
- **Q6 occurrence/effect audit** (promote after Q2–Q5): per-occurrence choice liveness —
  Prop-only-and-erased vs flows-into-Type, instance constructions (`Fintype.ofFinite`),
  finite-search repair candidates, residual capability, and explicit `unknown` when dependent
  flow cannot be classified safely.
- **Presentation-diamond benchmark** (after the presentations issue and Q6): start with
  `Finite ↔ Fintype`, `Countable ↔ Encodable`, `Set.Finite ↔ Finset` only; per direction
  record computability, required selection interface, supplied-vs-recovered data, and
  statement/proof-route consequences. Typeclass instrumentation v1 records only the *selected*
  instance and whether it came from a parameter, local construction, or global instance —
  "alternatives considered" is unstable elaborator telemetry, deferred.
- Deferred horizons: universal mechanical slicer (a restricted single-frontier slicer only
  after replay works: monomorphic, nondependent occurrences, human-stabilized output),
  tactic-search/failed-branch archaeology (discovery archaeology ≠ theorem strength),
  historical `#rm_diff` across arbitrary revisions.

## Further programs (roadmap-only horizons)

- **Constructive/intuitionistic RM**: not a separate database — a refined *logic context*
  (classical / intuitionistic / minimal / +MP / +LPO / +LLPO / +FAN / choice fragments).
  Constraint on #5 now: the context type must be extensible and must not hard-code classical
  logic. Seed MP/LPO/LLPO/fan/choice-fragment principles as exact literature records after #5.
- **Choice and maximality sub-zoo** (after #5/#6, preferably after one algebra case): unique /
  finite / countable / dependent / global choice, BPI/ultrafilter, Zorn-style maximality,
  representative selection, measurable selection — explicitly *not* one chain.
- **Finite, bounded, and feasible RM**: the Q-track's sibling (Q asks what bounds a proof
  yields; finite RM asks which finite forms are equivalent over weak finite foundations;
  feasible RM asks whether bounds live in practical complexity classes). Meeting point with
  `native_decide` trust, certified algorithms, and proof complexity.
- **Ordinal analysis and conservation backend**: ordinal notations, well-ordering principles
  (already forced by Dickson/WO(ω^ω)), reflection, cut elimination, conservativity,
  interpretability, proof speed-up — the vertical resolution the Big Five lack.
- Nonstandard RM, set-theoretic RM, further reducibilities (Medvedev, Muchnik, enumeration,
  strong Weihrauch, game), concrete incompleteness, categorical/structural RM, and RM of type
  theory itself (truncation, resizing, extensionality) remain named horizons.

## The quantitative proof-mining track (orthogonal: Q1, Q2, …)

Kohlenbach supplies the quantitative axis. Simpson classifies theorem strength; RMZoo records
the horizontal implication graph; quantitative proof mining records what bounds, moduli, finite
approximations, or oracle-relative programs can be recovered from a proof. This track cuts
across several tranches and is deliberately numbered separately (Q1, Q2, …) — it does not wait
for tranche 8.

- Q1. Quantitative normal forms: witness, bound, rate, metastability, modulus, finite
  approximation, oracle-relative program.
- Q2. Metastability vocabulary and interval/challenge-function API.
- Q3. Kohlenbach Proposition 2.27: explicit metastability for bounded monotone sequences.
- Q4. Finite convergence principle, including the [0,C] bound.
- Q5. Executable rational/dyadic bounded-search realizer.
- Q6. Occurrence/effect audit: Prop → Prop, Prop → Type, finite-search repair, residual oracle.
- Q7. Quantitative certificate registry: uniform parameters, intensional dependencies, term
  class, residual oracles, source hash.
- Q8. Herbrand/ε-weakening of WKL and EFILC.
- Q9. Finite-query quantitative Hall.
- Q10. Modulus-of-uniqueness pilot.
- Q11. Quantitative IVT and Heine–Cantor — distinguishing approximate zeros, quantitative
  interval localization, metastable/finite formulations, and a uniform exact-zero selector
  (four different targets; the issue must not silently aim at the strongest).
- Q12. Monotone convergence and Bolzano–Weierstrass metastability — distinguishing a full
  convergent-subsequence/cluster-point selector, weak BW (Cauchy subsequence without a rate),
  finite convergence principles, and metastable BW bounds.
- Q13. System-T IR, evaluation, and majorization.
- Q14. Negative translation and monotone functional interpretation.
- Q15. Mean ergodic theorem metastability comparison with mathlib.
- Q16. Bar-recursive/oracle-relative extraction horizon.

In the rich catalog, quantitative relations appear as:

```
qualitativeVariant ──herbrandizesTo──► metastableVariant
metastableVariant  ──realizedBy──────► extractedTerm
extractedTerm      ──majorizedBy─────► explicitBound
```

Legacy RMZoo export omits these fields; rich JSON retains them. A small vertical experiment
(Q2–Q5) should land after the conceptual-identity/statement-variant layer and inform the typed
fact and evidence design before it is finalized. The experiment stays **out of the general
fact registry initially** — it produces ordinary mathematical artifacts (Q2: precise
metastability and interval/challenge-function definitions; Q3: the formalized Kohlenbach
Prop. 2.27 bound; Q4: finite convergence with the exact [0,C]/rounding convention documented;
Q5: an executable rational/dyadic function with a correctness theorem and evaluated examples)
— and only then asks what the catalog must record: qualitative and metastable statement
variants, uniform parameters, extracted-program identity, correctness evidence,
majorant/bound relationships, intensional proof dependencies, residual oracles, and source
edition + hash. That empirical pressure shapes #5/#6.

## Issue acceptance checklist

Every theorem/principle issue finishes with: an exact statement variant; presentation
assumptions; a Simpson/RMZoo/literature citation; semantic scope; an honest evidence status; a
Lean proof or an explicit pending field; dependency/frontier audit output; an RMZoo alias or an
explicit statement that none exists; separate upper-bound and reversal status; no `sorry` in
the stable mathematical root.

Source stability: pinned mathlib revision and declaration/body hash for mined ports; exact
upstream commit and source line for imported RMZoo records; edition and theorem number for
books; source identity kept separate from the current display name.

Quantitative issues (Q-track) additionally finish with: the exact quantitative normal form; an
explicit input presentation; the parameters in which the output is uniform; the supplied
moduli/bounds on which it depends; the output term and its soundness theorem; the computational
class; residual oracle/principle effects; the distinction between a bound and a
witness-producing program; and no "rate of convergence" claim where only metastability is
possible.

## References

- **[Sim09]** Stephen G. Simpson, *Subsystems of Second Order Arithmetic*, 2nd edition,
  Perspectives in Logic, Cambridge University Press / Association for Symbolic Logic, 2009.
- **[Koh08]** Ulrich Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in
  Mathematics*, Springer Monographs in Mathematics, Springer, 2008.
- **[San]** Sam Sanders, *Reverse Mathematics: there and back again*, book manuscript,
  <https://sasander.wixsite.com/academic/book>.
- **RMZoo**: E. P. Astor et al., *The Reverse Mathematics Zoo*,
  <https://github.com/ericastor/rmzoo> (MIT license); documentation at
  <https://rmzoo.math.uconn.edu/documentation/>.
- **Weihrauch**: V. Brattka and G. Gherardi, *Weihrauch Degrees, Omniscience Principles and
  Weak Computability*, <https://arxiv.org/abs/0905.4679>; V. Brattka, G. Gherardi, and
  A. Marcone, *The Bolzano–Weierstrass Theorem is the Jump of Weak Kőnig's Lemma*,
  <https://arxiv.org/abs/1101.0792>; further per-row citations in the concordance workbook.
- **Concordance workbook**: `reverse_mathematics_concordance.xlsx` — 121 variant-fixed rows
  across the five treatment axes with per-row confidence, source keys, and URLs; the primary
  catalog seed (see "Treatment axes and the concordance workbook" above).

## Near-term sequence

Hall walking slice → catalog/RMZoo seam → tree and matching representation matrix → ω-model
calibrations → Simpson's WKL/ACA matching equivalences → RT²₂/SRT²₂/COH non-Big-Five slice →
coded analysis ladder.
