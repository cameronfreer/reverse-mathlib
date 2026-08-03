# reverse-mathlib

**A typed, proof-carrying atlas of mathematical strength and proof architecture in Lean.**
It records exact statement variants, presentations, represented uniform problems, and
concrete proof artifacts under several deliberately noncollapsed analyses: ordinary and
strict reverse mathematics, higher-order reverse mathematics, Weihrauch reducibility,
quantitative proof mining, and mathlib-specific proof-route archaeology.

The name has a double meaning: conventional **reverse mathematics** — which principles
suffice or are necessary over a weak base — and **reverse-engineering mathlib** — which
ideas, representations, interfaces, and proof routes are embodied in its declarations. The
project studies not only the weakest principles known to prove a theorem, but which route a
particular proof takes, which stronger ambient resources make a standard or elegant
transformation possible, what the statement's presentation supplies, and what witnesses,
oracle behavior, or quantitative data the proof produces.

> **Today it certifies facts about particular Lean proofs and ambient factorizations.** Some
> are candidates for genuine reverse-mathematical bounds after suitable interpretation
> bridges. Others are final results in their own right: canonical, overpowered, generic,
> quantitative, or presentation-revealing proof routes that should never be mistaken for
> minimal theorem calibrations. It is not currently proving anything over RCA₀ — the
> registry correctly reports zero certified bounds at every scope (ω-model / all-model /
> syntactic).

*Classify the theorem, preserve the proof, and never confuse the two.*

- **[ABOUT.md](ABOUT.md)** — what each layer actually establishes, how it relates to classical
  reverse mathematics, and the assurance routes toward genuine `RCA₀ ⊢ …` results.
- **[ROADMAP.md](ROADMAP.md)** — Simpson as the vertical theorem spine, RMZoo as the
  horizontal principle graph, the strict-RM and quantitative tracks, and the issue tranches.
- **Live zoo**: <https://cameronfreer.github.io/reverse-mathlib/> — the ambient-factorization
  graph, the catalog, and the canonical
  [`catalog.direct.json`](https://cameronfreer.github.io/reverse-mathlib/catalog.direct.json).

## What exists today

- **Dependency miner** (`#rm_deps`, `#rm_frontier`, hard `#rm_assert_*` CI gates): exact
  statement/value/proof-only closures over elaborated declarations; raw closures are never
  cut; assertions fail on truncated graphs.
- **The Hall walking slice**: mathlib's infinite Hall theorem mined at its compactness
  boundary and refactored as kernel-checked relative theorems —
  `WeakKonig ⇄ EFILC → CountableHall`, all in unrestricted Lean, composed end-to-end from
  mathlib's order-theoretic Kőnig lemma to `Classical.countableHall_nat`. CI certifies the
  proof-only closures exclude the topological route.
- **A typed catalog**: concepts (`reverse-mathlib:wkl`) ≠ exact statement variants
  (`wkl.binaryTree.ambient`) ≠ Lean interfaces, with registered semantic layers, typed
  external references (`rmzoo:` / `simpson:` / `concordance:` / `sanders:`), direction-aware
  typed certificates, and import-wide collision detection.
- **A quantitative pilot** (`ReverseMathlib/Quantitative/`): Kohlenbach's metastability of
  bounded monotone sequences (Prop. 2.27, Cor. 2.28) with an executable rational realizer and
  its finite-query locality theorem — bounds, not rates; see
  [docs/quantitative-pilot.md](docs/quantitative-pilot.md).
- **A deterministic exporter and site**: canonical JSON extracted from the elaborated
  environment's persistent extension state, rendered to the Pages site on every push.

## Structure

- `ReverseMathlib/` — mathematical root: `Standard/` principle statements, `Slice/` relative
  proofs, `Classical/` outright instances, `Quantitative/` the Q-track. Sorry-free, standard
  axioms only, `warningAsError` with the mathlib linter set.
- `ReverseMathlib/Registry.lean` — tooling root: `Meta/` (miner, registry, catalog, exporter),
  `Ports/` (catalog seed and port records). Never imported by the mathematical root.
- `ReverseMathlibExperimental/`, `ReverseMathlibFixtures/` — staging and collision-test
  libraries; never imported by production roots.
- `scripts/` — CI gates: sorry boundary and root isolation, axiom audits for both roots,
  miner micro-tests and the hard dependency assertions.
- `tools/zoo/` — the `rmlib-zoo` build/check/serve/diff CLI.

## Building

Pinned to Lean `v4.32.0` and the matching mathlib revision.

```sh
lake exe cache get
lake build
```

Useful commands once built (import `ReverseMathlib.Registry`): `#rm_deps <decl>`,
`#rm_frontier <decl>`, `#rm_concepts`, `#revmath_registry`, `#revmath_port? countableHall`,
`#revmath_stats`.

## License

Apache 2.0; see [LICENSE](LICENSE).

<p align="center">
  <img src="assets/header.png" alt="Robot miners with lanterns excavating glowing crystals from a night-time mine, its entrance stones carved with RCA₀, WKL₀, ACA₀, ATR₀, and Π¹₁-CA₀." width="820">
</p>
