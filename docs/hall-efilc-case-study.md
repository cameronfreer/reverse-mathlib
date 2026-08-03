# Hall–EFILC: compiling a mined proof route across several semantics

> **Status snapshot:** this case study describes reverse-mathlib at commit
> [`4fea2b5`](https://github.com/cameronfreer/reverse-mathlib/commit/4fea2b5), where the
> certified scoreboard is **ω-model: 3 / all-model: 0 / syntactic: 0**. Later work may add
> evidence, but it does not retroactively strengthen any claim made at this checkpoint.

This is a worked account of reverse-mathlib's first end-to-end experiment. It explains how
dependency mining exposed a compactness boundary inside mathlib's countable Hall proof, how
that boundary became an explicit finite inverse-limit principle, and how the resulting route
was certified at several deliberately distinct scopes.

The short version is:

$$
\text{mine a proof}
\longrightarrow
\text{discover a capability boundary}
\longrightarrow
\text{refactor through it}
\longrightarrow
\text{calibrate it at explicit scopes}
\longrightarrow
\text{reuse the certified bridges}.
$$

The claim is **not** that a dependency graph proves a theorem over $\mathsf{RCA}_0$. Mining
discovers and audits a route through one particular Lean proof. Reverse-mathematical meaning
enters only through separately checked internalizations, representations, semantic contexts,
and statement adapters.

The engineering economy is therefore not “encoding-free.” It is **encoding-amortized**:
coding and adequacy work is concentrated in reusable interfaces and backends instead of being
repeated inside every ordinary theorem proof.

## 1. What the Hall proof revealed

Mathlib's infinite Hall proof has the recognizable mathematical architecture

$$
\text{finite Hall}
+
\text{compactness for coherent finite approximations}
\Longrightarrow
\text{countable Hall}.
$$

Its implementation reaches generic topology, inverse-limit machinery, categorical/cofiltered
infrastructure, and matching-selection scaffolding. Those are excellent ambient tools, but
they obscure the smaller capability actually used by the argument.

The dependency miner separates three closures of an elaborated declaration $d$:

$$
\begin{aligned}
\operatorname{Stmt}(d) &= \text{constants required by the type of }d,\\
\operatorname{Val}(d) &= \text{constants reached from its proof or body},\\
\operatorname{ProofOnly}(d) &= \operatorname{Val}(d)\setminus\operatorname{Stmt}(d).
\end{aligned}
$$

The distinction matters. A statement may already package compactness in a typeclass or
structure argument, while two proofs of the same proposition may take very different routes.
The miner therefore reports exact facts about a **proof artifact**, not the intrinsic or
minimal strength of a theorem.

For Hall, the mined route suggested a smaller interface: compactness for a sequential system
of explicitly enumerated nonempty finite fibers with adjacent bonding maps. reverse-mathlib
calls this interface **explicit finite inverse-limit compactness** (EFILC). The acronym and
the exact Lean presentation are project-defined; the underlying finite-approximation and
Kőnig-style compactness pattern is standard.

The refactored ambient theorem is

```text
ExplicitFiniteInverseLimitCompactness → CountableHall
```

and the same ambient layer proves

```text
WeakKonig ⇄ ExplicitFiniteInverseLimitCompactness.
```

These are kernel-checked factorizations in unrestricted Lean. They do not by themselves say
that $\mathsf{RCA}_0+\mathsf{WKL}$ proves Hall. The residual proof could still use set
formation, recursion, induction, choice, quotients, or representation conversions whose
weak-system meaning has not been supplied.

The miner nevertheless has two durable jobs:

1. **Discovery:** it exposes a reusable capability boundary hidden inside a large proof.
2. **Architectural regression:** after refactoring, hard dependency gates require the new
   proof to reach finite Hall while excluding mathlib's infinite Hall theorem, the generic
   inverse-limit compactness theorem, and the matching-selection route.

Those gates preserve the chosen route. They neither prove that the route is optimal nor turn
the ambient theorem into an $\mathsf{RCA}_0$ derivation.

## 2. Why the “explicit” in EFILC matters

EFILC says, schematically:

> Given explicitly enumerated nonempty finite fibers and adjacent bonding maps, there is a
> coherent section through the system.

The supplied enumerations are part of the presentation. In a weak theory, “this set is
finite” and “here is a finite list enumerating it” are not interchangeable for free.
Recovering a list from an abstract finiteness assertion may require additional enumeration or
comprehension strength. The calibration is therefore attached to the exact
`explicitSequential.enumeratedFibers` variant, not to an unqualified phrase such as “finite
inverse limits are nonempty.”

That presentation gives a useful amortizable cut:

$$
\mathsf{WKL}\longleftrightarrow\mathsf{EFILC}
\longrightarrow T_1,T_2,T_3,\ldots
$$

Hall is the first consumer. Its level-$n$ fiber consists of explicitly enumerated injective
partial transversals on the first $n$ indices. Finite Hall proves that each fiber is nonempty;
truncation supplies the bonding map; an EFILC section decodes to an infinite injective
transversal. A later theorem with the same finite-approximations/coherent-limit shape can
reuse the compactness calibration without reproducing the entire binary-tree construction.

## 3. Internalizing the route over Turing ideals

The first foundational target was semantic and model-facing. An `OmegaPart` is a designated
collection $\Omega\subseteq\mathcal P(\mathbb N)$. `IsTuringIdeal Ω` requires nonemptiness,
downward closure under set-based Turing reducibility, and closure under recursive join. Every
recursive set then belongs to $\Omega$.

Inputs and outputs are required to be internal to $\Omega$:

- sets are ambient subsets of $\mathbb N$ paired with proofs of membership in $\Omega$;
- functions are total, single-valued, graph-coded internal sets;
- mathematical statements use the relational `MapsTo` surface rather than a selected
  evaluation function.

Each construction follows four layers:

1. define the raw ambient set or graph;
2. prove an explicit relative-computability theorem for it;
3. use Turing-ideal closure to package it as internal data;
4. prove mathematical correctness, allowing hypotheses that must not affect the data flow.

This permits classical Lean reasoning as proof scaffolding without pretending that an
arbitrary ambient set belongs to the model. Internality follows from a named reduction to
data already in the ideal.

### EFILCω implies WKLω

Given an internal infinite binary tree, the compiler enumerates each level structurally,
forms an inverse system of level-node codes, and uses truncation as the bonding map. EFILC
supplies a section. The decoder constructs a path whose graph is reducible to the section
graph alone. The tree is read by the compiler; the answer alone is read by the decoder.

The integrated theorem is `weakKonigAt_of_efilcAt`.

### WKLω implies EFILCω

Given an internal inverse system, the compiler constructs a binary tree of finite coherent
transcripts. All unbounded search is confined to the two graph-lookup channels while finite
transcripts are materialized; the verifier after those transcripts is primitive recursive.
The tree is reducible to the join of the fiber and bonding graphs, hence internal. WKL
supplies a path, which is decoded into a section whose graph is reducible to the join of the
fiber graph and path answer. Bonding information is used to prove correctness, not by that
decoder.

The integrated theorem is `efilcAt_of_weakKonigAt`.

### EFILCω implies Hallω

For the exact Hall input, an `InternalHallFamily` carries both a candidate relation and a
duplicate-free candidate enumerator, together with a checked equivalence between them. The
fiber compiler's type accepts only the enumerator; the relation can enter only the
correctness proof. Finite Hall proves level nonemptiness, EFILC supplies a coherent section,
and the decoder produces an internal injective transversal from the section answer alone.

The integrated theorem is `countableHallAt_of_efilcAt`.

At checkpoint `4fea2b5`, these routes support two positive certified leaves:

| Exact semantic fact | Checked status |
| --- | --- |
| `WKLω ⇔ EFILCω` | Kernel-checked over every `IsTuringIdeal` context |
| `EFILCω → Hallω` | Kernel-checked upper implication over every `IsTuringIdeal` context |

The composite `WKLω → Hallω` is deliberately derived rather than registered as another
leaf. Computed closure must not inflate the catalog's certified-fact count.

## 4. The independent Type-2 (Weihrauch) lens

The same data-access profiles were then realized independently in the
[computable-analysis](https://github.com/cameronfreer/computable-analysis) machine model and
ingested at pinned revisions. These theorems were not extracted from the ω-model proofs, and
the ω-model facts were not inferred from them.

| Exact represented reduction | What its type certifies |
| --- | --- |
| `WKL ≤sW EFILC` | The section-to-path postprocessor cannot access the original tree input |
| `EFILC ≤W WKL` | A certified ordinary reduction; it does **not** assert that no strong reduction exists |
| `Hall ≤sW EFILC` | The compiler reads the Hall enumerator, and the postprocessor reads the section answer alone |

This is representation-relative evidence about uniform problem transformations. It is not a
second proof of the Turing-ideal theorems. The agreement is useful precisely because two
typed lenses, with different semantics and certification mechanisms, independently expose
the same input-access structure.

As on the ω side, closure remains a computed view: `Hall ≤W WKL` follows from the imported
leaves by weakening strong reducibility and transitivity, but is not imported as a fourth
record.

## 5. What is certified—and what remains pending

The checkpoint's positive results have three different readings:

| Claim | Status at `4fea2b5` |
| --- | --- |
| `∀ Ω, IsTuringIdeal Ω → (WKLAt Ω ↔ EFILCAt Ω)` and the Hall implication | Kernel-checked |
| Reading these as consequences over the ω-models of $\mathsf{RCA}_0$ | Literature-backed context reading; formal context and exact statement adequacy pending |
| An object-language derivation such as $\mathsf{RCA}_0+\mathsf{WKL}\vdash\mathsf{Hall}$ | Not established |
| `∃ Ω, IsTuringIdeal Ω ∧ ¬ WKLAt Ω`; its use toward $\mathsf{RCA}_0\nvdash\mathsf{WKL}$ | Countermodel kernel-checked; forward context adequacy, exact WKL adequacy, and backend soundness pending for the turnstile claim |

The distinction is permanent. An ω-model theorem says nothing by itself about nonstandard
first-order parts, so it cannot be promoted to all-model validity or a syntactic derivation.

There are four assurance branches, not one ladder:

1. **Turing-ideal internalization.** The route already taken yields checked consequences over
   every Turing ideal. With exact context adequacy—or at least the direction from
   object-language $\mathsf{RCA}_0$ ω-modelhood to `IsTuringIdeal`—and exact statement
   adequacy, these become formal $\omega$-model consequences. They still do not become
   turnstile theorems.
2. **All-model semantics.** Translate exact variants into a suitable object language, prove
   the constructions valid in every model of the base theory, and use an appropriate
   completeness theorem for the chosen first-order, many-sorted, or Henkin presentation to
   obtain a positive syntactic theorem.
3. **Restricted replay.** Replay the residual proof against an approved Lean capability
   surface, then prove that fragment interpreted in or conservative over the object theory.
   The replay proves fragment membership; the interpretation theorem gives it
   reverse-mathematical meaning.
4. **Countermodel and soundness.** For a negative turnstile result, exhibit a semantic
   countermodel, prove the **forward** context adequacy
   `IsTuringIdeal Ω → MΩ ⊧ RCA₀` needed to make it a model of the base, prove exact statement
   adequacy, and apply soundness. Completeness and all-model validity are unnecessary.

The last asymmetry is important: positive derivability through semantics needs all-model
validity and completeness; negative derivability can be refuted by one adequate model and
soundness.

## 6. REC and the Kleene tree: the negative control

The checkpoint's third certified fact is a different evidence shape:

```text
rca0Core ⊭ω WKL
```

Its certificate is an explicit countermodel. `recursivePart`—the sets recursive without an
oracle—is a Turing ideal. The file `Omega/KleeneTree.lean` builds a recursive infinite binary
tree with no recursive path by bounded diagonalization: at length $n$, it inspects the first
$n$ diagonal computations for $n$ steps and flips every observed output bit. Membership is
primitive recursive, prefix closure follows from time-bound monotonicity, nodes exist at
every level, and a purported recursive path eventually contradicts its own diagonal bit.

Thus REC contains the tree but no path through it, yielding
`not_weakKonigAt_recursivePart`. The registered `SemanticNonimplicationCertificate` stores
the countermodel rather than treating a missing dependency or a failed search as evidence of
nonimplication.

This is the constructive counterpart to the permanent warning:

> Dependency presence cannot prove a reversal, and dependency absence cannot prove a
> nonimplication.

The REC/WKL route is a **negative control** for the Hall–EFILC architecture, not a third
calibration of EFILC. Its dependency gates reach the Kleene tree and bounded evaluator while
excluding both WKL–EFILC compilers and the Hall route. That independence checks that EFILC is
a reusable interface where it is mathematically relevant, not a universal intermediary
forced into every result.

Once forward Turing-ideal-to-$\mathsf{RCA}_0$ context adequacy, exact binary-tree WKL
adequacy, and backend soundness are formalized, this countermodel can support a checked
$\mathsf{RCA}_0\nvdash\mathsf{WKL}$ result. No completeness theorem is needed for that
negative conclusion.

## 7. What was amortized, and what was not

The case study has demonstrated that reverse-mathlib can:

- discover a stable mathematical capability inside a real mathlib proof;
- refactor the proof through that capability and pin its route in CI;
- internalize exact presentations over Turing ideals with explicit computability proofs;
- certify direction and semantic scope with typed certificates;
- independently realize the same input-access architecture as represented reductions;
- register countermodel-backed nonimplications without deriving them from dependency data.

It has not demonstrated a general automatic compiler from arbitrary mathlib proofs to
$\mathsf{RCA}_0$ derivations. The ω-model construction was hand-built and required sequence
codes, graph-coded functions, finite oracle transcripts, primitive-recursive verifiers, and
presentation-specific correctness proofs. Future extraction and transfer automation can
amortize recurring obligations; it cannot make representation coding or adequacy theorems
disappear.

The right summary is:

> **Not encoding-free, but encoding-amortized; not proof extraction by mining alone, but
> mining-guided factorization followed by certified target-relative transfer.**

## 8. Open presentation and provenance obligations

The exact lower bound for the one-sided Hall relation-plus-enumerator presentation remains
open. The pinned corpus audit found no matching reversal in the audited RMZoo, Simpson, and
Hirst material. Known perfect-matching and society formulations cannot be transferred without
an explicit presentation bridge; “not found in this corpus snapshot” is not a novelty claim
or a nonimplication.

The Kleene-tree attribution is also deliberately qualified:

- [ ] Verify S. C. Kleene, *Recursive functions and intuitionistic mathematics*, Proceedings
  of the 1950 International Congress of Mathematicians, and the comparison to Simpson
  §VIII.2, against pinned source snapshots.

Until that task is complete, the attribution remains **claimed and unverified against a
pinned primary-source snapshot**. This provenance status does not affect the kernel-checked
construction.

The source artifacts behind this snapshot are:

- ambient boundaries: `ReverseMathlib/Slice/WeakKonigEfilc.lean` and
  `ReverseMathlib/Slice/HallFromCompactness.lean`;
- Turing-ideal constructions: `ReverseMathlib/Omega/`;
- typed registrations: `ReverseMathlib/Ports/Omega/WklEfilc.lean`,
  `HallEfilc.lean`, and `RecWkl.lean`;
- route and composition gates: `scripts/MetaSmoke.lean`;
- exact evidence records and projections: the
  [live atlas](https://cameronfreer.github.io/reverse-mathlib/).

Together they illustrate the project's governing rule: **classify the theorem, preserve the
proof, and never confuse the two.**
