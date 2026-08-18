/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.JumpClosure
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The seventh production ω fact: injection-range existenceω ⇔ jump closureω
(issue #49)

The **atomic registration**: over every Turing ideal, every internal graph-coded
injection has an internal range iff the part is closed under the Turing jump. At
registration this pair was literature-positioned above the WKL circle with no
certified comparison edge; the comparison edge arrived with the eighth fact
(`jumpClosureBoundedKonigOmega`), which certifies jump closure → bounded Kőnig and
retired the literature band.

**Presentation discipline** (pinned in review): the range side is the **exact
injection-graph presentation** of `InternalFunction` — the presentation the sixth
certified fact froze — never formula-coded range existence. The jump side is a
**semantic closure property**, never a theorem-strength principle. **No ACA-labeled
endpoint or fact**: no arithmetical-comprehension adapter is proved, and the
identification of jump ideals with ACA₀'s ω-models stays a literature-backed
reading (Hirst thesis §1.4, consulted in the verified primary source; the corpus
claims and this prose necessarily mention ACA₀ — nothing registered carries the
label).

Routes, each through its own reduction spine (gated in `scripts/MetaSmoke.lean`,
including the negative gates: neither direction reaches the other):

* **jump closure → range existence**: `range_le_jump` (one curry-mapped jump
  query) plus ideal downward closure;
* **range existence → jump closure**: `jumpEnumGraph_le` internalizes the jump
  enumeration's graph, the total injective packaging, and `range_jumpEnum`
  rewrites its internal range to the jump set.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_concept injectionRangeExistence where
  statement := "Injection-range existence: every injective function has a range — \
    for every injection f there is a set containing exactly the values of f"
  description := "Injection-range existence as a conceptual family (Hirst thesis \
    Theorem 1.4, statement verified verbatim in the primary source; its proof is \
    deferred there to Simpson, cf. [Sim09] III.1.3, literature-backed). The \
    registered presentation is the exact injection-graph form; formula-coded, \
    arbitrary-function, and enumeration presentations join only once their \
    adapters are proved. No ACA-labeled endpoint or fact: no \
    arithmetical-comprehension adapter is proved"

rm_concept jumpClosure where
  statement := "Jump closure: the Turing jump of every set in the collection is \
    again in the collection — a semantic closure property of second-order parts, \
    distinguishing the jump ideals among the Turing ideals"
  description := "A semantic closure-property node, not a theorem-strength \
    principle: it names the closure condition the equivalence calibrates against, \
    so the fact has an honest typed endpoint. Hirst thesis §1.4 identifies the set \
    domains of ACA₀'s ω-models as the jump ideals — that identification stays \
    literature-backed; it carries no external crosswalk"

rm_statement_variant injectionRangeExistence.injectionGraphs.turingIdealOmega where
  concept := injectionRangeExistence
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.InjectionRangeExistenceAt
  description := "Injection-range existence at a second-order part: every internal \
    graph-coded injective function has an internal range — a set containing exactly \
    the function's values — all stated relationally through graph membership. The \
    exact injection-graph presentation, shared with the disjoint-range separation \
    variant; never formula-coded range existence"

rm_statement_variant jumpClosure.turingIdealClosure.turingIdealOmega where
  concept := jumpClosure
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.JumpClosedAt
  description := "Jump closure at a second-order part: the Turing jump of every \
    internal set (the self-halting codes relative to it, through the oracle-code \
    evaluator) is again internal. A closure property of the part, packaged as a \
    capability so the equivalence has a typed endpoint"

/-- **The exact ω-model equivalence certificate**: over every Turing ideal,
injection-range existence holds iff the part is jump closed. Visibly composed from
the two named direction theorems — `injectionRangeExistenceAt_of_jumpClosedAt`
(through `range_le_jump` and downward closure) and
`jumpClosedAt_of_injectionRangeExistenceAt` (through `jumpEnumGraph_le` and
`range_jumpEnum`) — and nothing else; the dependency gates in
`scripts/MetaSmoke.lean` pin both routes and forbid each direction from the
other. -/
theorem injectionRange_jumpClosure_omega_equivalence :
    Meta.SemanticEquivalenceCertificate IsTuringIdeal
      InjectionRangeExistenceAt JumpClosedAt :=
  ⟨fun _ h => ⟨fun hr => jumpClosedAt_of_injectionRangeExistenceAt h hr,
    fun hj => injectionRangeExistenceAt_of_jumpClosedAt h hj⟩⟩

rm_fact injectionRangeExistenceJumpOmega equivalence where
  base := rca0
  scope := omegaModels
  lhs := [injectionRangeExistence.injectionGraphs.turingIdealOmega]
  rhs := [jumpClosure.turingIdealClosure.turingIdealOmega]
  note := "Over every Turing ideal, injection-range existence in its exact \
    injection-graph formulation is equivalent to closure under the Turing jump. \
    The literature places this pair above weak Kőnig's lemma; the certified \
    comparison edge to the WKL circle arrived with the eighth fact \
    (jumpClosureBoundedKonigOmega). \
    Provenance: Hirst thesis Theorem 1.4 (statement verified verbatim in the \
    pinned primary source; proof deferred there to Simpson, cf. [Sim09] III.1.3, \
    literature-backed). No ACA-labeled endpoint or fact: no \
    arithmetical-comprehension adapter is proved, and the jump-ideal \
    identification stays a corpus-recorded reading, never a registered crosswalk"

revmath_certify_fact injectionRangeExistenceJumpOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.injectionRange_jumpClosure_omega_equivalence
  note := "Composed from the two named direction theorems: \
    injectionRangeExistenceAt_of_jumpClosedAt (jump closure → range existence, \
    through range_le_jump and ideal downward closure) and \
    jumpClosedAt_of_injectionRangeExistenceAt (range existence → jump closure, \
    through jumpEnumGraph_le, the total injective packaging, and range_jumpEnum); \
    both route spines and their mutual exclusion are pinned by dependency gates \
    in scripts/MetaSmoke.lean"

end ReverseMathlib.Ports
