/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Corpus
import ReverseMathlib.Ports.ComputableAnalysis
import ReverseMathlib.Ports.Omega.HallEfilc
import ReverseMathlib.Ports.Omega.JumpClosureFact
import ReverseMathlib.Ports.Omega.FinitelyBranchingKonigFact
import ReverseMathlib.Ports.Omega.MatchingLocallyFiniteFact
import ReverseMathlib.Ports.Mathlib.HeineCantor

/-!
# The Hall variant audit (issue #7, first corpus-backed fixture)

What Simpson, Hirst, and RMZoo classify; how those statements differ from
`hall.oneSidedRelationEnumerator` (and the ω variant
`countableHall.oneSidedInjective.enumeratedCandidates.turingIdealOmega`); and exactly
which bridge would be required before any reversal transfers.

**Audit outcome — no match in the audited corpus; the exact lower bound remains open.**
The three honest outcomes of a variant audit are: (1) exact match found; (2) explicit
presentation bridge found or proved; (3) no match in the audited corpus, in which case
the exact question *remains open* — never "new": novelty would require separate priority
evidence, which this audit does not supply. This audit's outcome is (3):

* **RMZoo** (pinned database revision): no Hall/marriage/transversal principle symbol
  exists. The sole trace of the marriage literature is a commented-out — hence
  never-ingested — attribution of a *graph-coloring* equivalence to Hirst's marriage
  paper, preserved verbatim below.
* **Simpson** (SOSOA, 2nd ed.): §X.3 contains matching-theorem material at X.3.15/X.3.16,
  already recorded as *related variants* of the countable-Hall concept — two-sided /
  perfect-matching style, not the one-sided enumerated formulation. The exact statements
  were not re-consulted verbatim in this audit; no classification is transcribed.
* **Hirst** (marriage theorems, 1987 thesis and 1990 paper): calibrates marriage theorems
  for countable *societies* — presentations with boys, girls, and a relation, with
  boundedness/enumeration data varying by theorem — reportedly reaching WKL₀-level
  results for bounded presentations and stronger systems otherwise. The society
  presentations differ from the one-sided relation-plus-enumerator problem; nothing was
  verified verbatim, and no classification is transcribed.

Both missing bridges are recorded explicitly below; until a named theorem discharges one,
no corpus reversal transfers to the exact one-sided variants, and the catalog's own
certified state is unchanged: upper results only, scoreboard untouched.
-/

namespace ReverseMathlib.Ports

rm_namespace hirst "Jeffry Hirst — Combinatorics in Subsystems of Second Order \
  Arithmetic (PhD thesis, Pennsylvania State University, 1987) and 'Marriage theorems \
  and reverse mathematics' (Logic and Computation, Contemp. Math. 106, AMS, 1990) — \
  references"

rm_corpus_source rmzoo "e92f57acf072115744e818cabd0ac13f2e724754"
  "github.com/ericastor/rmzoo at the pinned commit (2024-03-27); database file \
   results.txt consulted in full"

rm_corpus_source simpson "2nd edition, Perspectives in Logic, ASL/Cambridge, 2009"
  "Subsystems of Second Order Arithmetic; section citations only — the text was not \
   re-consulted verbatim for this audit"

rm_corpus_source hirst "1987 thesis; 1990 paper in Contemp. Math. 106"
  "Marriage-theorem calibrations; bibliographic citations only — the texts were not \
   re-consulted verbatim for this audit"

rm_namespace hirstThesisPdf "Jeffry Hirst — Combinatorics in Subsystems of Second \
  Order Arithmetic, 1987 PhD thesis, the scanned PDF as served at \
  hirstjl.github.io/bib/pdf/jhthesis.pdf; pages 6-8 (Theorems 1.1-1.5 and §1.4 \
  ω-models) and pages 12-19 (Theorems 2.2 and 3.1, condition H_sym, and the \
  Chapter 2-3 proof passages) consulted directly — a verified source, distinct \
  from the bibliographic-only hirst namespace"

rm_corpus_source hirstThesisPdf
  "sha256:64070db6f0f81d9066f723f911debadaa9d4594ecf6c131a4026d3cd5fa288f4"
  "Verified download of the scanned thesis PDF. Chapter 1 records are \
   statement-level anchors (proofs deferred there to Simpson [50]); the \
   Chapter 2-3 marriage records also read the proof passages (pp. 13, 18, 19)"

rm_presentation_family oneSidedEnumeratedFamily "One-sided families: an ℕ-indexed family \
  of finite candidate sets, transversal injective into the candidates; presentation \
  supplies the candidate relation and/or an explicit enumerator (this catalog's exact \
  Hall variants live here)"

rm_namespace normannSanders "Dag Normann and Sam Sanders — Pincherle's theorem in \
  reverse mathematics and computability theory, arXiv:1808.09783 v6 (31 Jan 2020); \
  §1 and Appendix A consulted directly — a verified source"

rm_corpus_source normannSanders
  "sha256:01874ca1032eb3ac71f4f364c139e724b39056e51a2f477be73291704de46717"
  "Verified download of arXiv:1808.09783 v6. HBU and Corollary A.2 read verbatim; \
   the historical attributions (Dini, Pincherle, Bolzano, Young, Hardy, Riesz, \
   Lebesgue) carry the paper's own caveat and stay attributed interpretations"

rm_presentation_family gaugeCoverFormulation "Gauge (canonical-cover) formulations: \
  a point-indexed family of positive radii generating the covering by intervals \
  (x − Ψ(x), x + Ψ(x)), finite subcovers as finite center sequences — [NS18]'s HBU \
  shape, distinct from countable-cover, sequential, and attainment compactness"

rm_presentation_family oneSidedMarriageSystem "One-sided marriage systems: societies \
  whose solution matches every boy; finiteness a property, never enumerated"

rm_presentation_family twoSidedMarriageSystem "Two-sided marriage systems (societies): \
  boys, girls, and a compatibility relation, with two-sided solution conditions and \
  presentation-dependent boundedness/enumeration data"

rm_presentation_family perfectMatchingFormulation "Perfect-matching formulations: \
  matchings exhausting one or both sides of a bipartite system, Simpson X.3-style"

rm_presentation_family injectionRangeFormulation "Injection-range formulations: an \
  injection f : N → N with its range Ran(f) — Hirst thesis Chapter 1 notation, \
  functions in Simpson's set-of-pairs coding"

rm_presentation_family omegaModelSemantics "ω-model semantic characterizations: the \
  corpus describes classes of second-order set domains (Turing ideals, jump ideals) \
  rather than a problem formulation; only closure-property-level claims can be \
  transcribed"

rm_presentation_family finitelyBranchingTreeFormulation "Finitely-branching tree \
  formulations: trees of finite sequences in lh(σ)/σ(n) notation — Hirst thesis \
  Chapter 1. The supplied-bound form (Theorem 1.1) and the levelwise-bound form \
  (Theorem 1.3: for every length a bound on the last entries exists) are distinct \
  presentations calibrating to different subsystems"

rm_presentation_family unrepresentedFormulation "No formulation present: the corpus \
  contains no principle for this concept at the pinned revision"

rm_corpus_claim rmzooHallAbsent where
  source := rmzoo "results.txt (whole file, pinned revision)"
  family := unrepresentedFormulation
  concepts := [countableHall, wkl]
  wording := verbatim "#    WKL <-> COLORk \"Hirst (1990) - Marriage theorems and \
    reverse mathematics\""
  claim := "The pinned RMZoo database contains no Hall, marriage, or transversal \
    principle symbol. The quoted line — the only trace of the marriage literature — is \
    commented out (never ingested) and attributes a graph-coloring equivalence, not a \
    marriage theorem, to Hirst's paper. Outcome for this corpus: no match; nothing to \
    transfer."

rm_corpus_claim simpsonMatchingSections where
  source := simpson "X.3.15–X.3.16"
  family := perfectMatchingFormulation
  concepts := [countableHall]
  wording := absent
  claim := "Matching-theorem material at the cited sections, already registered as \
    related variants of the countable-Hall concept: two-sided / perfect-matching style, \
    not the one-sided enumerated formulation. Not re-consulted verbatim in this audit; \
    no classification is transcribed, and none transfers without the recorded bridge."

rm_corpus_claim hirstMarriageCalibrations where
  source := hirst "1987 thesis; 1990 paper"
  family := twoSidedMarriageSystem
  concepts := [countableHall, wkl]
  wording := absent
  claim := "Reported calibrations of marriage theorems for countable societies, with \
    the subsystem depending on the presentation's boundedness/enumeration data — \
    reportedly WKL₀-level for bounded presentations. Society presentations differ from \
    the one-sided relation-plus-enumerator problem; nothing verified verbatim in this \
    audit; no classification is transcribed, and none transfers without the recorded \
    bridge."

rm_corpus_claim hirstInjectionRangeAca where
  source := hirstThesisPdf "p. 7, Theorem 1.4"
  family := injectionRangeFormulation
  concepts := [injectionRangeExistence]
  wording := verbatim "Theorem 1.4: (RCA₀) The following are equivalent: i) ACA₀. \
    ii) If f : N → N is an injection, then the set Ran(f) = {y ∈ N : ∃x f(x) = y} \
    exists."
  claim := "The classical ACA₀ calibration of injection-range existence, read \
    verbatim from the verified scan (source symbols preserved; only spacing \
    normalized). The thesis defers the proof to Simpson [50] (cf. [Sim09] \
    III.1.3, literature-backed). The registered ω-fact calibrates exactly the \
    internal injection-graph presentation against the jump-closure property; no \
    ACA-labeled endpoint or fact is registered."

rm_corpus_claim hirstBoundedKonigWkl where
  source := hirstThesisPdf "p. 6, Theorem 1.1"
  family := finitelyBranchingTreeFormulation
  concepts := [wkl]
  wording := verbatim "Theorem 1.1: (RCA₀) The following are equivalent: i) WKL₀. \
    ii) If T is a tree and h : N → N is a function such that for every τ ∈ T \
    ∀n < lh(τ)(τ(n) < h(n)), then there is an infinite path for T. (Here lh(τ) \
    denotes the length of τ and τ(n) denotes the nᵗʰ element of τ.)"
  claim := "The classical WKL₀ calibration of König's lemma with a SUPPLIED \
    dominating function h, read verbatim from the verified scan (source symbols \
    preserved; only spacing normalized). This is the supplied-data presentation \
    the fourth fact's explicitly bounded variant internalizes (bound as a \
    graph-coded internal function); it is a different presentation from the \
    levelwise-bound form of Theorem 1.3, and the two calibrate to different \
    subsystems. Proofs are deferred there to Simpson [50], literature-backed."

rm_corpus_claim hirstFinitelyBranchingKonigAca where
  source := hirstThesisPdf "p. 7, Theorem 1.3"
  family := finitelyBranchingTreeFormulation
  concepts := [finitelyBranchingKonig]
  wording := verbatim "Theorem 1.3: (RCA₀) The following are equivalent: i) ACA₀. \
    ii) (König's Lemma) If T is a finitely branching tree, that is, \
    ∀n ∃k ((σ ∈ T ∧ lh(σ) = n) → σ(n−1) < k), then there is an infinite path \
    for T."
  claim := "The classical ACA₀ calibration of full (merely) finitely-branching \
    König, read verbatim from the verified scan (source symbols preserved; only \
    spacing normalized; the displayed conjunction is transcribed ∧). The \
    branching bound is a levelwise PROPERTY — for every length a bound on the \
    last entries exists — never supplied data; the registered ninth fact's \
    interface retains exactly these quantifiers, with the positionwise form \
    derived through prefix closure, and the infinitude hypothesis our statement \
    carries is stated separately in the thesis (p. 5). Proofs are deferred there \
    to Simpson [50], literature-backed; the registered ω-fact calibrates against \
    the jump-closure property, and no ACA-labeled endpoint or fact is \
    registered."

rm_corpus_claim hirstOneSidedMarriageAca where
  source := hirstThesisPdf "p. 12, Theorem 2.2; reversal pp. 13, 19"
  family := oneSidedMarriageSystem
  concepts := [locallyFinitePerfectMatching]
  wording := verbatim "Theorem 2.2 (RCA₀) The following are equivalent: i) ACA₀ \
    ii) Any marriage problem in which each boy knows only finitely many girls, \
    and in which condition H is satisfied, has a solution."
  claim := "The one-sided infinite marriage calibration, read verbatim from the \
    verified scan (source symbols preserved; only spacing normalized). Recorded \
    as REVERSAL PROVENANCE ONLY: its reversal (p. 13) constructs the gadget the \
    tenth fact's reverse route reuses symmetrically (p. 19: 'The proof of the \
    reversal is immediate from the proof of Theorem 2.2. Since the relation R of \
    the previous proof is symmetric, condition H_sym holds'). NON-TRANSFER \
    CAVEAT: this society formulation carries finiteness as a property and no \
    enumerator, so no classification here transfers to the catalog's one-sided \
    countable-Hall variants (relation-plus-enumerator presentations) without a \
    proved presentation bridge, and none is registered — the standing Hall \
    honesty boundary is untouched."

rm_corpus_claim hirstSymmetricConditionHsym where
  source := hirstThesisPdf "p. 17, §3.1"
  family := twoSidedMarriageSystem
  concepts := [locallyFinitePerfectMatching]
  wording := verbatim "We will say that a marriage problem satisfies condition \
    H_sym if every subset of n boys knows at least n girls and every subset of n \
    girls knows at least n boys."
  claim := "The symmetric marriage condition, read verbatim from the verified \
    scan (source symbols preserved; only spacing normalized; the same page fixes \
    'symmetric solution' as a one-to-one matching of the set of boys onto the \
    girls). The registered tenth fact's interface carries exactly this two-sided \
    condition in cardinality form — every duplicate-free finite list of boys has \
    at least as many distinct joint acquaintances, witnessed by a duplicate-free \
    list, and conversely — as a separate hypothesis, never a structure field."

rm_corpus_claim hirstSymmetricMarriageAca where
  source := hirstThesisPdf "p. 18, Theorem 3.1"
  family := perfectMatchingFormulation
  concepts := [locallyFinitePerfectMatching, finitelyBranchingKonig]
  wording := verbatim "Theorem 3.1 (RCA₀) The following are equivalent: i) ACA₀ \
    ii) Any marriage problem in which each person knows only finitely many \
    members of the opposite sex, and in which condition H_sym is satisfied, has \
    a symmetric solution."
  claim := "The classical ACA₀ calibration of the symmetric marriage theorem, \
    read verbatim from the verified scan (source symbols preserved; only spacing \
    normalized). Local finiteness is a PROPERTY of the society ('knows only \
    finitely many'), never enumerated data — the registered tenth fact's \
    interface keeps it an existential property on each side of one bare edge \
    set. The thesis proves i) → ii) 'using König's lemma for arbitrary finitely \
    branching trees' via the partial-solution tree (p. 18), which is exactly the \
    registered forward route; the registered ω-fact calibrates against full \
    finitely-branching Kőnig (the ninth fact's concept), and no ACA-labeled \
    endpoint or fact is registered."

rm_corpus_claim nsHeineBorelUncountable where
  source := normannSanders "p. 11 (HBU)"
  family := gaugeCoverFormulation
  concepts := [gaugeHeineBorel]
  wording := verbatim "a functional Ψ : ℝ → ℝ⁺ gives rise to the canonical \
    covering ⋃_{x∈I} I_x^Ψ for I ≡ [0, 1], where I_x^Ψ is the open interval \
    (x − Ψ(x), x + Ψ(x)). Hence, the uncountable covering ⋃_{x∈I} I_x^Ψ has a \
    finite sub-covering by the Heine-Borel theorem; in symbols: \
    (∀Ψ : ℝ → ℝ⁺)(∃⟨y₁, . . . , y_k⟩)(∀x ∈ I)(∃i ≤ k)(x ∈ I^Ψ_{y_i})."
  claim := "The uncountable/gauge Heine–Borel principle HBU, read from the \
    verified download with the source typography (blackboard ℝ, superscript-plus \
    ℝ⁺) preserved; sub- and superscripts are transcribed with _/^ markers and \
    spacing normalized — the only normalizations. The registered ambient \
    capability keeps exactly this shape — point-indexed positive radii in, a \
    finite sequence of centers out — with centers in the interval by type, the \
    faithful reading of a finite subcover of the canonical covering. [NS18]'s \
    placement of HBU above the countable-cover form in higher-order RM is \
    reported as literature context only — neither certified nor transferred to \
    the registered ambient interfaces, which carry no degree or subsystem claim."

rm_corpus_claim nsUniformHeine where
  source := normannSanders "Appendix A, Corollary A.2, p. 38"
  family := gaugeCoverFormulation
  concepts := [uniformHeine, gaugeHeineBorel]
  wording := verbatim "Corollary A.2. For any ε >_ℝ 0 and g : (I × ℝ) → ℝ⁺, \
    there is δ >_ℝ 0 such that for any f : I → ℝ with modulus of continuity g, \
    we have (∀x, y ∈ I)(|x − y| <_ℝ δ) → |f(x) − f(y)| <_ℝ ε),"
  claim := "The hidden-uniformity Heine conclusion, read from the verified \
    download with the source typography (blackboard ℝ, superscript-plus ℝ⁺) \
    preserved; the subscript-ℝ comparisons are transcribed as >_ℝ and <_ℝ, \
    spacing is normalized, and the source's trailing punctuation is retained — \
    the only normalizations. The quantifier order ∀g,ε ∃δ ∀f is the content: δ \
    depends only on the local-control data, never on the controlled function. \
    The registered ambient principle totalizes g over ℝ → ℝ → ℝ (values outside \
    [0,1] × (0,∞) ignored) — a totalized presentation of the source's \
    subtype-domained modulus, not a literal identity. Appendix A's historical \
    proof attributions stay attributed interpretations under the paper's own \
    caveat; nothing historical is claimed."

rm_corpus_claim hirstLowWklOmegaModel where
  source := hirstThesisPdf "p. 8, §1.4, Theorem 1.6"
  family := omegaModelSemantics
  concepts := [wkl, jumpClosure]
  wording := verbatim "Theorem 1.6: There is an ω-model of WKL₀ in which every \
    set is of low degree, i.e. for each set X in the model, if a = deg(X), then \
    a′ ≤ 0′."
  claim := "A low ω-model of WKL₀, read verbatim from the verified scan (source \
    symbols preserved; only spacing normalized; the thesis credits the \
    Shoenfield–Kreisel low basis theorem). Read against the jump-ideal claim on \
    the same page: no jump ideal is low, since it contains 0′, so a WKL₀ ω-model \
    need not be jump closed. This was the recorded literature basis for the \
    atlas's former band placement of the jump family above the WKL circle; the \
    certified comparison edge (jump closure → bounded Kőnig, the eighth fact) \
    has since replaced the band, while this direction — a WKL₀ ω-model that is \
    not jump closed — stays literature-backed and uncertified, and no \
    separation edge is registered."

rm_corpus_claim hirstJumpIdealOmegaModels where
  source := hirstThesisPdf "p. 8, §1.4 (ω-models)"
  family := omegaModelSemantics
  concepts := [jumpClosure]
  wording := verbatim "The set domains of ω-models of ACA₀ are called jump ideals. \
    A jump ideal is a Turing ideal closed under the jump operation. Thus every \
    ω-model of ACA₀ contains every finite jump of 0."
  claim := "The jump-ideal characterization of ACA₀'s ω-model set domains, read \
    verbatim from the verified scan (source symbols preserved; only spacing \
    normalized). This is the literature reading behind the registered jump-closure \
    concept's positioning; it stays a reading — no ACA-labeled endpoint or fact and \
    no crosswalk is registered, and the registered fact's endpoints are the \
    injection-range and jump-closure capabilities only."

rm_presentation_bridge twoSidedToOneSidedEnumerated where
  family := twoSidedMarriageSystem
  to := uniformProblem hall.oneSidedRelationEnumerator
  requires := "A checked correspondence between two-sided society presentations \
    (including their boundedness/enumeration data) and the one-sided \
    relation-plus-enumerator problem, at the relevant scope. Until it lands, no society \
    classification — in particular no reversal — transfers to this exact problem."

rm_presentation_bridge perfectMatchingToOneSidedOmega where
  family := perfectMatchingFormulation
  to := statement countableHall.oneSidedInjective.enumeratedCandidates.turingIdealOmega
  requires := "An exact correspondence between perfect-matching formulations (Simpson \
    X.3.15/X.3.16 style) and the one-sided enumerated-candidates variant at the \
    Turing-ideal ω layer. Until it lands, no matching classification — in particular no \
    reversal — transfers to this exact variant."

rm_presentation_family sourceUnspecifiedFormulation "The corpus names the principle by \
  symbol without fixing an exact formulation in the database itself; only concept-level \
  claims can be transcribed"

rm_corpus_claim rmzooWklFormRPi12 where
  source := rmzoo "results.txt lines 418 and 569 (duplicate occurrences, both preserved)"
  family := sourceUnspecifiedFormulation
  concepts := [wkl]
  wording := verbatim "WKL form rPi12"
  claim := "RMZoo classifies WKL's syntactic form as rPi12 — restricted Π¹₂ in the sense \
    of Hirschfeldt and Shore (2007), per the pinned README's form list. Operator \
    semantics from the pinned operator ledger ('form' = syntactic-form classification); \
    the only relation in the pinned database whose complete endpoint expression resolves \
    through the exact-alias crosswalk. Two source occurrences, both preserved; \
    deduplication belongs to this normalization only. Concept-level; no fact or edge \
    registered."

rm_corpus_audit hallVariantAudit
  "The Hall variant audit: RMZoo (pinned database revision), Simpson SOSOA 2nd ed. \
   §X.3.15–X.3.16 (section citations), and Hirst's marriage-theorem calibrations (1987 \
   thesis; 1990 paper), audited against the exact one-sided relation-plus-enumerator \
   problem hall.oneSidedRelationEnumerator and its ω variant"
  "No matching reversal found in the audited corpus; the exact lower bound remains open. \
   Not 'new': novelty would require separate priority evidence, which this audit does \
   not supply. Both required presentation bridges are recorded and MISSING."

end ReverseMathlib.Ports
