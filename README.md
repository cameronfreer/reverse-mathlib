# reverse-mathlib

**A typed, proof-carrying atlas of mathematical strength and proof architecture in Lean**
— conventional reverse mathematics and reverse-engineering mathlib, analyzed side by side
under several deliberately noncollapsed lenses (ordinary/strict/higher-order RM,
Weihrauch reducibility, proof mining, proof-route archaeology). *Classify the theorem,
preserve the proof, and never confuse the two.*

[Live atlas](https://cameronfreer.github.io/reverse-mathlib/) ·
[What the claims mean](ABOUT.md) ·
[Hall–EFILC case study](docs/hall-efilc-case-study.md) ·
[Roadmap](ROADMAP.md)

> **Scoreboard — checked scoped results: ω-model: 7 (kernelChecked); all-model: 1
> (backendChecked); syntactic: 1 (backendChecked).** The all-model entry is the exact
> backend-checked `Rca0Theory ⊭ wklSentence` over all general (Henkin-style) L₂
> structures; the syntactic entry is the exact backend-checked
> `Rca0Theory ⊬ wklSentence in l2VarWitnessLK.v1` (the bridge's pinned standard
> calculus — a fully specified LK presentation of the two-sorted logic assumed in
> Simpson §I.2, with direct soundness and no completeness claim). Neither is ever an
> unqualified conventional-RCA₀ claim.
> No unqualified `RCA₀ ⊢ …` or `RCA₀ ⊬ …` turnstile claim exists at any scope; scopes and
> presentations are never promoted, and derived closure results are computed, never
> registered.

## What it does

- **Mines proof routes**: exact statement/value/proof-only dependency closures over
  elaborated Lean declarations (`#rm_deps`, `#rm_frontier`), with hard `#rm_assert_*`
  CI gates that fail on truncated graphs — proof-route archaeology, not strength labels.
- **Extracts capabilities**: boundaries found inside ordinary mathlib proofs — the first
  is EFILC, the explicit finite inverse-limit compactness inside mathlib's infinite Hall
  proof — refactored into kernel-checked relative theorems and represented uniform
  problems.
- **Certifies at explicit scopes**: a typed catalog where concepts ≠ exact statement
  variants ≠ Lean interfaces, with direction-aware typed certificates against registered
  semantic contexts, and route gates that keep every claimed proof architecture checked.

## Certified results

All seven facts are kernel-checked over **every Turing ideal** against the
`rca0.turingIdealOmega` context; the identification of Turing ideals with RCA₀'s
ω-models is literature-backed. A `⊭ω` fact is a countermodel-witnessed model-class
separation, never a turnstile underivability claim.

| Fact | Statement | Notes |
| --- | --- | --- |
| `wklEfilcOmega` | WKLω ⇔ EFILCω | the first capability calibration |
| `efilcHallOmega` | EFILCω → Hallω | upper implication only; Hall's reversal is an audited open question |
| `rca0CoreWklOmega` | RCA₀-core ⊭ω WKL | REC countermodel through an explicit bounded-computation Kleene tree |
| `boundedKonigWklOmega` | bounded-Kőnigω ⇔ WKLω | explicitly bounded (the bound is supplied data); never full finitely-branching Kőnig, which is ACA-level and a separate concept |
| `wklTwoRegularMatchingOmega` | 2-regular matchingω ⇔ WKLω | enumerated-neighborhood refinement of Shafer/Hirst; the perfect-matching-to-one-sided presentation bridge stays MISSING |
| `disjointRangeSeparationWklOmega` | disjoint-range separationω ⇔ WKLω | the exact injection-graph presentation (Hirst Thm 1.2 (ii)); never generic Σ⁰₁ separation — formula-coded adapters unproved |
| `injectionRangeExistenceJumpOmega` | injection-range existenceω ⇔ jump closureω | the first fact above the WKL circle (Hirst Thm 1.4, verified in the pinned primary source); the jump side is a semantic closure property, and no ACA label appears — the jump-ideal identification stays literature-backed |

Detailed presentation caveats, certificate names, and pending bridges live on the atlas
cards and registration notes — each fact's card is the authority for its exact claim.

## Other checked evidence

Kept permanently distinct from the certified scoreboard:

- **Imported checked** Weihrauch reductions (`WKL ≤sW EFILC`, `EFILC ≤W WKL`
  certified-ordinary, `Hall ≤sW EFILC`), proved natively in
  [computable-analysis](https://github.com/cameronfreer/computable-analysis) at pinned
  revisions and ingested as external evidence — never axioms.
- **Backend** records from the
  [ω-semantics bridge](https://github.com/cameronfreer/reverse-mathlib-foundation), an
  external checked bridge to
  [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation):
  checked forward context realization and exact statement adapters for ŴKL/EFILC/Hall,
  plus calculus-relative nonderivability in the Henkin-safe calculus AND in the
  bridge's pinned standard calculus `l2VarWitnessLK.v1` (with logical equality; a
  typed comparison record states both calculi are independently sound and carries no
  embedding); **converse context adequacy** remains pending. Backend evidence never
  adds a local certified fact, graph edge, port, or closure edge — but the validated
  all-model countermodel record (`Rca0Theory ⊭ wklSentence`, witnessed by the
  ω-structure over REC) and the validated standard-calculus nonderivability record
  (`Rca0Theory ⊬ wklSentence in l2VarWitnessLK.v1`) contribute the two explicitly
  backend-qualified scoped results above.
- **A quantitative pilot**: Kohlenbach's metastability of bounded monotone sequences with
  an executable rational realizer — bounds, not rates
  ([docs/quantitative-pilot.md](docs/quantitative-pilot.md)).
- **Reported** corpus findings (RMZoo, Simpson, Hirst, at pinned snapshots) with missing
  presentation bridges named explicitly; an absence finding means not found in the
  snapshot, never a mathematical negation.

## The first program

reverse-mathlib's first program mines Lean proofs for WKL-shaped compactness routes: the
mined EFILC capability is certified equivalent to binary-tree WKL at the ω layer and
mutually Weihrauch-reducible with it at the represented layer, while countable Hall
remains a downstream upper-bound consumer whose reversal is an audited open question. The
REC/WKL separation is the program's negative control — route gates prove it touches none
of the EFILC machinery, so the capability is a discovered boundary, not a universal
intermediary. The full worked example is the
[Hall–EFILC case study](docs/hall-efilc-case-study.md).

## Repository map

- `ReverseMathlib/` — mathematical root: `Standard/`, `Slice/`, `Classical/`, `Omega/`,
  `Quantitative/`. Sorry-free, standard axioms only.
- `ReverseMathlib/Registry.lean` — tooling root: `Meta/` (miner, registry, exporter) and
  `Ports/` (catalog and registrations). Never imported by the mathematical root.
- `scripts/` — CI gates: sorry/root boundaries, axiom audits for both roots, and the
  architectural regression suite (`MetaSmoke.lean`).
- `tools/zoo/` — the `rmlib-zoo` build/check/serve/diff CLI behind the live atlas and the
  canonical
  [`catalog.direct.json`](https://cameronfreer.github.io/reverse-mathlib/catalog.direct.json).

## Building

Pinned to Lean `v4.32.2` and the matching mathlib revision.

```sh
lake exe cache get
lake build
```

Useful commands once built (import `ReverseMathlib.Registry`): `#rm_deps <decl>`,
`#rm_frontier <decl>`, `#rm_concepts`, `#revmath_registry`, `#revmath_stats`.

## License

Apache 2.0; see [LICENSE](LICENSE).

<p align="center">
  <img src="assets/header.png" alt="Robot miners with lanterns excavating glowing crystals from a night-time mine, its entrance stones carved with RCA₀, WKL₀, ACA₀, ATR₀, and Π¹₁-CA₀." width="820">
</p>
