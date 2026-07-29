# reverse-mathlib

Lean 4 formalization work in reverse mathematics.

## Structure

- `ReverseMathlib/` — the root spine: sorry-free, standard axioms only, built with
  `warningAsError` and the mathlib linter set.
- `ReverseMathlibExperimental/` — staging area for work in progress. May contain
  sorries; must still typecheck; never imported by the root spine.
- `scripts/check_sorry_boundary.py` — enforces the boundary between the two.
- `scripts/AxiomAudit.lean` — verifies the spine depends only on `propext`,
  `Classical.choice`, and `Quot.sound`.

## Building

Pinned to Lean `v4.32.0` and the matching mathlib revision.

```sh
lake exe cache get
lake build
```

## License

Apache 2.0; see [LICENSE](LICENSE).
