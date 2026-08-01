/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Interchange
import ReverseMathlib.Ports.Catalog

/-!
# The computable-analysis import: represented WKL/EFILC reductions (issues #27/#28)

The first real payload through the #28 interchange channel: the represented WKL and EFILC
uniform problems, the Weihrauch and strong-Weihrauch reducibility notions, the named
crosswalks into the `computableAnalysis` namespace, and the ingestion of the two checked
reduction records exported at a pinned revision of `cameronfreer/computable-analysis`:

* `WKL ≤sW EFILC` (`ComputableAnalysis.wkl_le_efilc`) — the decoder reads the section
  answer alone, so the reduction is **strong**;
* `EFILC ≤W WKL` (`ComputableAnalysis.efilc_le_wkl`) — the decoder consults the input for
  the chunk widths, so the reduction is **ordinary**.

Both are proved there from the represented promises alone, independently of the certified
ω-model equivalence here; the input-access observations recorded with that equivalence
have thereby become typed, representation-relative classifications — held as **imported
external evidence**, never Lean axioms, in their own store (`#rm_imports`), contributing
to no certified count and crossing into no other fact family.
-/

namespace ReverseMathlib.Ports

rm_reducibility_notion weihrauch
  "Ordinary Weihrauch reducibility: fixed preprocessor and postprocessor transform every
   realizer of the target into a realizer of the source, the postprocessor seeing the
   original input alongside the oracle answer (cf. Brattka–Gherardi–Pauly, Weihrauch
   Complexity in Computable Analysis)"

rm_reducibility_notion strongWeihrauch
  "Strong Weihrauch reducibility: as `weihrauch`, but the postprocessor sees only the
   oracle answer"

rm_uniform_problem wkl.streamCodedTree where
  concept := wkl
  input := "Baire stream presenting a set of binary words positively and decidably: word \
    w is a node iff the stream is nonzero at the pinned word code of w; prefix closure \
    and a node at every level are promises inside the problem"
  output := "Cantor point: the bit stream of an infinite path through the presented tree"
  operation := single

rm_uniform_problem efilc.streamCodedFiberBonds where
  concept := explicitFiniteInverseLimitCompactness
  input := "Baire stream presenting a sequential inverse system: track 0 the codes of the \
    enumerated finite fiber lists, track 1 the adjacent bond values; nonempty fibers and \
    bonds landing in the fiber below are promises inside the problem"
  output := "Baire stream: a section — at every level a fiber element, coherent under \
    the bonds"
  operation := single

rm_uniform_problem hall.oneSidedRelationEnumerator where
  concept := countableHall
  input := "Baire stream presenting an ℕ-indexed family both ways at once: track 0 the \
    codes of the enumerated finite candidate lists, track 1 the positive decidable \
    candidate relation; the membership equivalence between them and the marriage \
    condition over the enumerated lists are promises inside the problem. One-sided"
  output := "Baire stream: an injective transversal — at every index a candidate of the \
    relation, no value chosen twice"
  operation := single

rm_external_ref computableAnalysis "weihrauch" exactAlias reducibilityNotion weihrauch
rm_external_ref computableAnalysis "strongWeihrauch" exactAlias reducibilityNotion
  strongWeihrauch
rm_external_ref computableAnalysis "wkl/streamCodedTree" exactAlias uniformProblem
  wkl.streamCodedTree
rm_external_ref computableAnalysis "efilc/streamCodedFiberBonds" exactAlias uniformProblem
  efilc.streamCodedFiberBonds
rm_external_ref computableAnalysis "hall/oneSidedRelationEnumerator" exactAlias
  uniformProblem hall.oneSidedRelationEnumerator

rm_import_reductions "imports/computable-analysis/wkl-efilc.json"
rm_import_reductions "imports/computable-analysis/hall-efilc.json"

end ReverseMathlib.Ports
