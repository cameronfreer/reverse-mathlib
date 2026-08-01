/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Corpus
import ReverseMathlib.Ports.ComputableAnalysis
import ReverseMathlib.Ports.Omega.HallEfilc

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

rm_presentation_family oneSidedEnumeratedFamily "One-sided families: an ℕ-indexed family \
  of finite candidate sets, transversal injective into the candidates; presentation \
  supplies the candidate relation and/or an explicit enumerator (this catalog's exact \
  Hall variants live here)"

rm_presentation_family twoSidedMarriageSystem "Two-sided marriage systems (societies): \
  boys, girls, and a compatibility relation, with solution conditions on both sides and \
  presentation-dependent boundedness/enumeration data"

rm_presentation_family perfectMatchingFormulation "Perfect-matching formulations: \
  matchings exhausting one or both sides of a bipartite system, Simpson X.3-style"

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

end ReverseMathlib.Ports
