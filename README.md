<p align="center">
  <img src="assets/header.png" alt="Robot miners with lanterns excavating glowing crystals from a night-time mine, its entrance stones carved with RCA₀, WKL₀, ACA₀, ATR₀, and Π¹₁-CA₀." width="820">
</p>

# reverse-mathlib

Reverse mathematics for Lean: proof-strength analysis of mathlib via dependency mining,
hand-written proof factorizations at named principle boundaries, and an evidence registry that
never overstates what has been established.

## The thesis

Proof-mine existing Lean developments, expose small principle boundaries, and certify those
boundaries separately — rather than formalizing an encyclopedia of reverse mathematics from
scratch, or stamping Big-Five labels on mathlib theorems (which would usually be false or
meaningless: a kernel-axiom audit is not a strength audit).

## Case study: the Hall walking slice

Mathlib's infinite Hall theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`) proves
a countable marriage theorem by routing finite matchings through a categorical inverse-limit
theorem backed by topological compactness (ultimately Tychonoff), extracting a matching with
`Classical.indefiniteDescription`. Its kernel axioms are just `propext`, `Classical.choice`,
`Quot.sound` — indistinguishable from a trivial lemma. The proof-only dependency closure is
where the structure lives, and this repository makes it visible and then replaces it:

- **`#rm_deps` / `#rm_frontier`** (`ReverseMathlib/Meta/`): exact dependency graphs with
  statement vs proof-only closures; the raw closure is never cut, the frontier view exhibits
  the compactness boundary as a cut point.
- **`ReverseMathlib.Slice.countableHall_of_finiteInverseLimitCompactness`**: countable Hall
  derived from `ExplicitFiniteInverseLimitCompactness` *taken as a hypothesis*. Levels are
  explicitly enumerated `Finset`s of encoded injective partial transversals; mathlib's *finite*
  Hall theorem (reused, not reinvented) proves each level `Finset.Nonempty` — no selection step,
  no topology.
- **Hard CI gates** (`scripts/MetaSmoke.lean`): `#rm_assert_proof_depends` /
  `#rm_assert_not_proof_depends` certify, on complete closures only, that mathlib's proof
  crosses the compactness boundary and the `hallMatchingsOn` selection scaffolding while ours
  contains neither — and does contain finite Hall.
- **The registry record** (`ReverseMathlib/Ports/Mathlib/Hall.lean`), verdict in full:

  ```
  source relation: proof analogue / mined architecture
  relative Lean factorization: kernel checked
  ambient: unrestricted Lean over standard ℕ
  RM semantic scope: none
  candidate classical classification: WKL₀ … [claimed, UNVERIFIED]
  backend RM certificate: pending
  exact lower bound: pending
  ```

That verdict is deliberately modest: in full Lean the principles are all provable, so the
implication as an ambient proposition does not calibrate reverse-mathematical strength — the
informative artifact is the *factorization of a particular proof term*, and nothing here claims
an ω-model or subsystem result. Those require the model-relative layer and a backend, which
come later and are recorded as `pending` until they exist.

One honest limitation, found while building the gates: `Classical.indefiniteDescription` is not
assertable at constant granularity — `Classical.em` itself reaches it, so every classical proof
does. The selection-free repair is an occurrence-level fact (the construction never extracts
from a `Nonempty` instance); occurrence-level auditing is future work.

The slice now closes end-to-end (`ReverseMathlib/Classical/KonigHall.lean`): mathlib's
order-theoretic Kőnig lemma → `Classical.weakKonig` → EFILC (via the relative bridge) →
countable Hall (via the relative Hall theorem) → `Classical.countableHall_nat`, with gates
certifying the chain reaches both bridges and finite Hall and never the infinite Hall theorem
or the topological inverse-limit theorem. Statement-variant caveat, recorded in the port: our
`CountableHall` is a *one-sided injective-choice* variant — related to, but not identical with,
Simpson's perfect-matching theorems X.3.15/X.3.16, and the ambient variant has no certified RM
classification.

## Structure

- `ReverseMathlib/` — mathematical root (`ReverseMathlib.lean`): `Standard/` principle
  statements over ℕ, `Slice/` relative proofs. Sorry-free, standard axioms only,
  `warningAsError` with the mathlib linter set.
- `ReverseMathlib/Registry.lean` — tooling root: `Meta/` (dependency miner, assertion commands,
  evidence registry), `Ports/` (registry records). Never imported by the mathematical root.
- `ReverseMathlibExperimental/` — staging area. May contain sorries; must typecheck; never
  imported by either production root.
- `scripts/` — CI gates: `check_sorry_boundary.py` (sorry boundary, meta/math isolation, no
  orphans), `AxiomAudit.lean` + `MetaAxiomAudit.lean` (standard axioms only, both roots, no
  exemptions), `MetaSmoke.lean` (miner micro-tests + the Hall dependency gates).

## Roadmap

See [ROADMAP.md](ROADMAP.md): Simpson as the vertical theorem spine, RMZoo as the horizontal
principle graph, and the long-term target of a typed, presentation-aware, proof-carrying
superset of the RMZoo database. Near-term work is tracked in the issues (walking-slice stretch,
then the catalog/RMZoo seam).

## Building

Pinned to Lean `v4.32.0` and the matching mathlib revision.

```sh
lake exe cache get
lake build
```

Useful commands once built (import `ReverseMathlib.Registry`): `#rm_deps <decl>`,
`#rm_frontier <decl>`, `#revmath_registry`, `#revmath_port? countableHall`, `#revmath_stats`.

## License

Apache 2.0; see [LICENSE](LICENSE).
