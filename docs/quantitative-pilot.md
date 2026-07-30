# Q2–Q5 pilot report: what the catalog needs for quantitative content

The pilot (`ReverseMathlib/Quantitative/`) formalized Kohlenbach's metastability analysis of
bounded monotone sequences — Proposition 2.27, Corollary 2.28, Remark 2.29 of [Koh08]
(printed pp. 31–32, PDF 48–49, SHA-256
`027d72cfa73b86616e85fa19a35ad10ffa7248eae13b364aa29a590933b81b45`) — as ordinary mathematics,
deliberately outside the fact registry. This report records what the experiment shows the
catalog (#5/#6 and the eventual quantitative certificate schema) must be able to express.

## What was built

- `Metastability.lean` (Q2): the quantitative spine (`challengeStep`, `candidate`,
  `metastabilityBound Φ(g,k)`, `finiteHorizon`, the `[0,C]` variants, the shared rational
  `dyadic` tolerance, inclusive `challengeInterval`, `MetastableAt`), with every off-by-one
  convention pinned by `example`s.
- `MonotoneSequence.lean` (Q3): the candidate ("moreover") theorem first —
  `∃ i ≤ C·2^k, MetastableAt … (candidate g i)` — then the headline bounded form
  `∃ n ≤ Φ(g,k), …`. The endpoint-drop core is generic over a linear ordered field and,
  notably, **needs no antitonicity** (only the bounds); monotonicity enters when localizing
  metastability to the endpoint condition.
- `FiniteConvergence.lean` (Q4): the finite convergence principle over
  `a : Fin (M(g,k,C) + 1) → ℝ` with constant extension, certifying the selected challenge
  interval lies below `M`. `C` is a natural; general bounds need a ceiling convention (later).
- `RationalSearch.lean` (Q5): the executable realizer `findMetastable : Option ℕ` (bounded
  search over the candidates; decidable because rational), with totality from bounds alone,
  a spec theorem, genuine metastability under antitonicity, the **locality theorem** (agreement
  through `M(g,k,C)` implies identical output — "only the finite prefix is queried"), and
  evaluated examples pinned by `#guard_msgs`.

## What the catalog must record (empirical findings)

1. **Qualitative real theorem vs rational uniform problem.** The metastability *bound* holds
   for real sequences; the *executable selector* exists for rational sequences because `<` is
   decidable. These are different objects: one statement variant (real, ambient), one uniform
   problem (rational representation, `Option ℕ` output). The `uniformizes` edge must carry the
   representation difference, not identify them.
2. **Parameters `g`, `k`, `C` are uniformity data.** The bound `Φ(g,k,C)` is uniform in the
   sequence and depends only on the challenge/precision/bound parameters. The certificate
   schema needs a per-result list of the parameters in which the output is uniform.
3. **Bound vs witness-producing program.** `exists_metastable_le_bound` provides a bound;
   `findMetastable` is a program. The schema must distinguish these (and never let "bound"
   render as "rate": no computable rate of convergence exists in general — a permanent caution
   on Q-records).
4. **Candidate index vs output location.** The search space is indexed by `i ≤ C·2^k`; the
   output is `n = candidate g i`. Both matter: complexity lives in the index space, queries in
   the location space.
5. **Representation and decidability requirements.** The realizer's existence is exactly the
   decidability of rational comparison. An exact real-number selector would require a
   comparison/representation **residual oracle** — the schema's residual-oracle field is not
   optional.
6. **Finite-prefix locality.** `findMetastable_congr` is the model finite-query certificate:
   agreement through the explicit horizon `M(g,k,C)` determines the output. Quantitative
   records should be able to cite such locality theorems as evidence.
7. **Intensional dependencies.** The realizer calls `g` (the challenge function) as an oracle;
   the count and pattern of those calls is meaningful structure the schema may eventually
   record.
8. **Source pinning.** Edition, printed and PDF pages, and content hash — recorded in the
   module docstrings here — belong in the provenance model as first-class fields.

## Non-findings worth recording

- Nothing here entered the fact registry; the theorems are ordinary mathematics under the
  standard axiom audit (all four headline declarations are swept).
- No claim of RCA₀-provability or of any RM classification is made by these files.
