# About the reverse-mathlib project

reverse-mathlib is a **typed, proof-carrying atlas** of statements, presentations, proof
routes, and resource use in Lean. It records both the extensional/contextual
classification of an exact theorem variant — always relative to a base, a semantic scope,
and a presentation, never "intrinsic" independently of them — and the architecture of
particular proofs of it;
reverse mathematics (ordinary, strict, higher-order), Weihrauch reducibility, quantitative
proof mining, and mathlib proof-route archaeology are distinct projections of that record —
none is the master ordering, and a route result ("this canonical proof overshoots the
theorem's known calibration") is a final result in its own right, not preliminary evidence
awaiting promotion. The slogan: *classify the theorem, preserve the proof, and never
confuse the two.*

For the complete worked example behind these distinctions, see the
**[Hall–EFILC case study](docs/hall-efilc-case-study.md)**, pinned to checkpoint `4fea2b5`.

## 1. What it is actually doing

There are several layers, with different meanings.

### Ordinary kernel-axiom audit

Lean can report that a proof transitively uses `propext`, `Classical.choice`, and
`Quot.sound`. This is exact as a Lean axiom statement but nearly useless for reverse
mathematics: a trivial classical lemma and a proof using Tychonoff may have the same three
axioms. Moreover, `Classical.em` itself is implemented through choice machinery, so merely
finding `Classical.indefiniteDescription` does not mean the mathematical proof performed a
serious selection.

### Declaration-level dependency mining

The miner (`ReverseMathlib/Meta/DepGraph.lean`) instead walks every constant in the
elaborated theorem type and proof body. It records type dependencies, value/proof
dependencies, inductive declaration-group dependencies, modules and instance status, complete
versus truncated traversal, and genuine unknown constants. It computes three closures:

- **statement closure** — everything required by the theorem's type;
- **value closure** — everything reached from the proof/body;
- **proof-only closure** — value closure minus statement closure.

That subtraction matters. If a theorem assumes `[CompactSpace X]`, much of its strength has
already been packaged into its statement; the proof itself may then be easy. Conversely, two
proofs of the same statement can have very different proof-only closures.

This is an exact syntactic fact about the current elaborated declaration — not a minimality
result, and not a claim about every proof of the theorem. The right name for this activity is
**proof-route archaeology**, not theorem-strength inference: finding a compactness theorem in
a proof closure says this proof uses it; removing it says this proof avoids that declaration;
neither rules out a different proof or a reconstruction of the same principle from unlisted
ingredients.

### Named frontiers

`#rm_frontier` takes selected declarations as recognizable boundaries and stops expanding
there:

```
finite Hall and matching construction
                 │
                 ▼
explicit finite inverse-limit compactness
                 │
                 ▼
countable Hall
```

The raw dependency graph remains unchanged; the frontier is a view of it. A frontier
annotation means "treat this declaration as one conceptual interface for this audit." It does
**not** automatically mean "this declaration is exactly WKL₀" — that calibration needs
separate evidence.

### Hand-written proof factorization

The mathematically strongest current artifact is an ordinary Lean theorem such as

```
ExplicitFiniteInverseLimitCompactness → CountableHall
```

The compactness principle is an explicit hypothesis — a binder in a relative theorem, never a
Lean axiom. The registry (`ReverseMathlib/Meta/Registry.lean`) stores a typed certificate
`RelativeCertificate P T` whose field has type `P → T`, and registration checks direction
(`upper`: `P → T`; `lower`: `T → P`; `exact`: `P ↔ T`) and that `P` and `T` definitionally
match the registered exact variants. An unrelated theorem such as `True.intro` cannot
masquerade as a certificate.

One important limitation: a theorem `P → T` proved in unrestricted Lean may use other
full-Lean principles in its body. The current certificate proves the conditional implication
in Lean, but not yet that the residual proof is RCA₀-level. The dependency gates provide
evidence about the route; **restricted replay** is still needed for the much stronger "uses
only this interface" claim.

### Dependency gates

CI proves facts such as: the mathlib Hall proof reaches the generic inverse-limit/Tychonoff
machinery; the refactored proof reaches finite Hall; the refactored proof does **not** reach
the named infinite-Hall theorem, topological inverse-limit theorem, or selection scaffolding;
and the graph was complete rather than truncated. These are useful architectural facts.
Negative dependency gates do not prove necessity, and they cannot rule out every
mathematically equivalent route through unclassified declarations.

### Presentation-aware catalog

The catalog keeps distinct:

| Layer | Example |
|---|---|
| concept | `reverse-mathlib:wkl` |
| exact statement variant | `reverse-mathlib:wkl.binaryTree.ambient` |
| Lean interface | `ReverseMathlib.Standard.WeakKonig` |
| represented uniform problem | binary path selection under a specified representation |

This prevents a common RM mistake: treating "WKL", arbitrary finitely branching Kőnig's
lemma, binary-tree path choice, and an ambient Lean theorem as one object.

### The current Hall chain

The current checked ambient graph is

```
WeakKonig ⇄ EFILC → CountableHall
```

All three arrows are kernel-checked relative factorizations in unrestricted Lean. They do
**not** yet say `WKL₀ ⊢ CountableHall`.

The three principles, briefly:

- **WeakKonig** — every prefix-closed binary tree (coded) with a node at every level has an
  infinite path.
- **EFILC** — *explicit finite inverse-limit compactness*: every sequential inverse system
  of **explicitly enumerated**, nonempty finite sets with adjacent bonding maps has a
  coherent section. "Compactness for systems of finite approximations" — the boundary the
  refactored Hall proof factors through: finite Hall makes each level of coded partial
  transversals nonempty, EFILC threads a coherent infinite transversal through them. The
  word *explicit* is doing reverse-mathematical work: supplied enumerations keep the
  principle at the intended WKL₀ calibration, where a merely-asserted-finite version may
  require additional enumeration/comprehension strength — the calibration is
  presentation-sensitive.
- **CountableHall** — the one-sided injective-transversal Hall statement (related to, not
  identical with, Simpson's perfect-matching X.3.15/X.3.16).

Each principle also has a **Turing-ideal ω form** (`WeakKonigAt`, `EFILCAt` in
`ReverseMathlib/Omega/`): the same statement internalized to a second-order part `Ω`, with
inputs presented by internal sets and graph-coded internal functions and outputs required to
belong to `Ω`. `WKLω ↔ EFILCω` over Turing ideals — with explicit relative-computability proofs
establishing internality (distinct from the Type-2 Weihrauch reductions) — **is the first
certified ω-model calibration**, and `EFILCω → Hallω` (upper
implication only) the second; both are reported as `⊨ω`, never as `⊢`.

### The current certified state, at three levels

| Result | Status |
| --- | --- |
| `∀ Ω, IsTuringIdeal Ω → (WKLω(Ω) ↔ EFILCω(Ω))`, `… → (EFILCω(Ω) → Hallω(Ω))`, `… → (bounded-Kőnigω(Ω) ↔ WKLω(Ω))` (the explicitly bounded presentation: the bound is supplied data), `… → (2-regular-matchingω(Ω) ↔ WKLω(Ω))` (the enumerated-neighborhood presentation — the first certified equivalence involving the countableHall family), and `∃ Ω, IsTuringIdeal Ω ∧ ¬WKLω(Ω)` (REC, the Kleene tree) | **Kernel-checked** (typed semantic certificates, scoreboard ω-model: 5 / all-model: 0 / syntactic: 0) |
| Reading these as `RCA₀ ⊨ω WKL ↔ EFILC`, `RCA₀ + WKL ⊨ω Hall` | Mathematically standard, **literature-backed** ([Sim09] VIII.1); backend object-syntax adequacy pending |
| `RCA₀ ⊢ WKL ↔ EFILC` (and `RCA₀ + WKL ⊢ Hall`) in checked object syntax | **Not established**; scopes are never promoted |

The composites (`WKLω → Hallω` through the certified leaves; `Hall ≤W WKL` through the
imported Weihrauch leaves) remain **derived closure results**, computable by any consumer
and registered by none — linked ports and derivable edges never inflate the unique-fact
scoreboard.

Two further evidence grades live alongside the certified facts, permanently distinct:

- **Imported checked** uniform reductions, proved natively in the
  [computable-analysis](https://github.com/cameronfreer/computable-analysis) machine model
  at pinned revisions and ingested through a versioned JSON interchange as external
  evidence — never Lean axioms, never certified counts: `WKL ≤sW EFILC` (decoder reads the
  section answer alone; strongness enforced by the postprocessor's type), `EFILC ≤W WKL`
  (**certified ordinary** — the theorem never asserts non-strong-reducibility), and
  `Hall ≤sW EFILC` for the exact one-sided relation-plus-enumerator presentation. These
  give the recorded input-access profiles typed, representation-relative meaning: the two
  lenses (ω-model and uniform) agree without either being inferred from the other.
- **Reported** corpus findings at pinned snapshots: what RMZoo (pinned database revision;
  no Hall/marriage symbol exists — its sole trace is a commented-out citation), Simpson
  (X.3.15/X.3.16, two-sided/perfect-matching family), and Hirst (society calibrations)
  classify, with source wording preserved apart from normalized concept-level claims, and
  the presentation bridges that would be required before any reversal transfers recorded
  explicitly as **MISSING**. Audit outcome: no matching reversal found in the audited
  corpus; the exact lower bound for the one-sided variant remains open — never "new"
  without separate priority evidence, and absence of evidence is never displayed as
  evidence of absence.

## 2. How this relates to existing reverse mathematics

Classical reverse mathematics asks, over a weak base such as RCA₀, whether
`RCA₀ ⊢ T ↔ P` for principles `P` like weak Kőnig, arithmetical comprehension, or transfinite
recursion. The project decomposes that large claim into smaller artifacts:

```
existing ordinary proof
        │
        ▼
P_Lean → T_Lean                    (kernel-checked relative theorem)
        │
        ▼
presentation/interpretation bridges
        │
        ▼
RCA₀ ⊢ P̂ → T̂
```

Existing RM literature contributes:

- **The right boundaries.** Binary-tree path existence for WKL, range existence for ACA,
  arithmetical transfinite recursion for ATR, and the many matching, compactness,
  convergence, completeness, and algebraic equivalents — excellent candidate frontiers around
  which ordinary Lean proofs can be refactored.
- **Known calibrations and reversals.** If a mined theorem factors through a binary
  compactness interface, the literature may already prove the appropriately coded interface
  equivalent to WKL₀ — a strong candidate upper bound; a known reversal for the exact variant
  supplies a candidate lower bound. But the exact formulation matters: the ambient one-sided
  countable Hall statement here is related to, but not identical with, Simpson's
  perfect-matching results X.3.15/X.3.16, so those classifications do not transfer
  automatically.
- **A calibration oracle for the miner.** A good development test: does mining an existing
  proof recover boundaries resembling the known reverse-mathematical decomposition? A
  completeness proof should ideally expose enumeration, Lindenbaum extension, Markov-like
  reasoning, and WKL-like compactness — not merely `Classical.choice`.
- **The horizontal principle graph.** RMZoo records implications, non-implications,
  conservation, conjunctions, and reducibilities below and around the Big Five;
  reverse-mathlib is building a richer typed layer around that knowledge (exact variants,
  semantic contexts, provenance, imported vs inferred facts, Lean certificates where
  available).
- **The quantitative axis.** Kohlenbach-style proof mining asks what bound, modulus,
  metastability guarantee, or oracle-relative program can be extracted — interacting with but
  distinct from qualitative strength. A theorem may be RCA₀-provable while its uniform
  witness-selection problem remains noncomputable under a chosen representation.

## 3. What confidence could this eventually provide about RCA₀ implications?

Three claim forms stay permanently distinct: `P_Lean → T_Lean` (ambient factorization),
`RCA₀ + P̂ ⊨ T̂` at ω-model or all-model scope (semantic consequence — the all-model form is
already a genuine RM upper bound), and `RCA₀ + P̂ ⊢ T̂` (checked object-language
derivability). None promotes to another automatically.

The assurance routes:

| Evidence | What it establishes | Confidence about RCA₀ ⊢ P → T |
|---|---|---|
| Dependency graph | Current Lean proof syntactically reaches certain declarations | None by itself |
| Frontier report | Current proof factors architecturally through named boundaries | Suggestive upper bound |
| Ambient relative theorem | Lean kernel checks P_Lean → T_Lean | Very high confidence in the conditional ordinary mathematics |
| Portability audit | Every construction, comprehension, induction, and choice occurrence carries a target-relative translation obligation, inventoried and discharged | Very strong evidence the proof formalizes over the base, encoding backend pending |
| Restricted replay | Residual proof checks using only an approved fragment/interface | Certified fragment membership — an RM bound only when paired with a fragment interpretation |
| Literature interpretation | Published mathematics identifies the fragment/variant with RCA₀ + P | High human mathematical confidence, not end-to-end Lean certification |
| Formal fragment interpretation | Lean proves the restricted fragment is interpreted by or conservative over RCA₀ | Formal RM upper bound for translated statements |
| ω-model certificate | Every ω-model (Turing ideal) of RCA₀ + P satisfies translated T | Certified ω-model consequence — not derivability |
| All-model certificate | Every model of RCA₀ + P satisfies translated T | Formal semantic RM result |
| Syntactic derivation | A checked object-theory derivation exists | Strongest direct formal certificate |

These rows are **routes, not rungs of one ladder**. There are two main branches from an
ambient factorization: the replay branch (portability audit → restricted replay → fragment
interpretation → syntactic theorem) and the model-facing branch (internalized proof → ω-model
and all-model certificates → completeness → syntactic theorem). Rows on different branches
are not ordered against each other: replay without an interpretation is neither above nor
below an ω-model theorem, and ω-model validity never promotes to all-model validity. An
all-model certificate and a syntactic derivation become interchangeable only once soundness
and completeness are themselves formalized — and even then a derivation is *more direct*, not
*truer*.

### The amortized bridge

Very high confidence is possible **without theorem-by-theorem encoding** — provided the
encoding is amortized rather than omitted. Suppose the project eventually has a restricted
Lean fragment `F` and proves once:

1. `F` is interpretable in or conservative over RCA₀ for the relevant sentence class;
2. the Lean capability `P_Lean` translates to the RM principle `P̂`;
3. the Lean statement `T_Lean` translates to `T̂`;
4. a particular proof replays inside `F + P_Lean`.

Then composition yields `RCA₀ + P̂ ⊢ T̂`, and thousands of theorem proofs can reuse that
bridge without each manipulating Gödel codes or raw second-order syntax. The hard coding does
not disappear — it is concentrated in the fragment interpretation, the model-facing
set/function API, the presentation adapters, each capability calibration, and the statement
translations. That concentration is the main economy of the project.

If the bridge remains external literature (Lean checks `fragment + WKL interface ⊢ T` while a
well-established published theorem says the fragment is conservative over WKL₀), the result
is comparable to an unusually transparent published RM proof: the mathematical body is
kernel-checked, the route auditable, the foundational bridge cited and reviewed, the exact
presentation recorded. That justifies a status like *literature-calibrated checked
factorization; candidate upper bound WKL₀* — and must not render as "Lean-certified over
RCA₀" until the bridge is formalized. Once it is, not writing every theorem directly in
second-order syntax is an engineering choice, not a foundational weakness.

## What proof mining can never establish alone

Three cautions are permanent:

1. **It establishes upper bounds on proofs, not minimal theorem strength.** A proof using WKL
   shows WKL suffices for that proof route; another proof may use less.
2. **It cannot produce lower bounds from dependency presence.** Proving that `T` implies WKL
   needs a reversal `RCA₀ ⊢ T → WKL` or an equivalent model argument.
3. **Dependency absence is not non-implication.** A proof avoiding ACA machinery shows
   neither that ACA is unnecessary in every proof nor that RCA₀ proves the theorem.
   Non-implications require separation models, conservation results, computability arguments,
   or formal countermodels.

The eventual ideal certificate for an exact equivalence is: **upper** — checked restricted
proof + certified fragment interpretation + certified statement adapters; **lower** — checked
reversal or countermodel theorem at the same exact variant and semantic scope.

The project's real contribution is making every component — and every missing component —
visible. It can avoid repeating the hard encoding inside each ordinary proof, but it cannot
honestly avoid having a trusted interpretation layer somewhere.
