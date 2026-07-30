/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Concepts
import ReverseMathlib.Standard.Trees
import ReverseMathlib.Standard.InverseLimit
import ReverseMathlib.Standard.Hall

/-!
# Conceptual catalog seed

The walking slice's conceptual families and their typed external references. Additive over the
capability registry (`Ports/Mathlib/*.lean`): concepts own no Lean propositions; the exact
Lean interfaces stay on today's capability entries until issue #4 migrates them to statement
variants. Only `exactAlias` references resolve; the Simpson/concordance entries here are
provenance.
-/

namespace ReverseMathlib.Ports

rm_namespace rmzoo "Reverse Mathematics Zoo symbols (github.com/ericastor/rmzoo, pinned \
  import arrives with issue #7)"
rm_namespace simpson "[Sim09] Simpson, Subsystems of Second Order Arithmetic, 2nd ed. — \
  section and theorem references"
rm_namespace concordance "reverse_mathematics_concordance.xlsx row identifiers — external \
  provenance, never canonical identity"
rm_namespace sanders "[San] Sam Sanders, Reverse Mathematics: there and back again, \
  monograph under review with Springer, pp 450, 2026 — references"

rm_concept wkl where
  description := "Weak Kőnig's lemma as a conceptual family: binary-tree formulations across \
    semantic layers (ambient / ω-model / second-order syntax); explicitly bounded \
    formulations may join once their relationship is fixed. Merely finitely branching \
    (full Kőnig) is the ACA-level principle and belongs to a separate concept, not under \
    the rmzoo:WKL alias"

rm_concept explicitFiniteInverseLimitCompactness where
  description := "Explicit finite inverse-limit compactness as a conceptual family: \
    sequential systems of explicitly enumerated finite fibers with adjacent bonding maps"
  label := "EFILC"

rm_concept countableHall where
  description := "Countable Hall / marriage as a conceptual family: the one-sided \
    injective-choice and perfect-matching (Simpson X.3.15/X.3.16) variants are related but \
    not identical, and no RMZoo symbol exists for this family"

rm_semantic_layer ambient "statements about standard ℕ in unrestricted Lean; provable \
  outright, no reverse-mathematical semantic scope"

rm_statement_variant wkl.binaryTree.ambient where
  concept := wkl
  layer := ambient
  interface := ReverseMathlib.Standard.WeakKonig
  description := "Binary-tree weak Kőnig on the ambient list-based surface: prefix-closed \
    Set (List Bool) with a node at every level has a path (Set ℕ of positions)"

rm_statement_variant efilc.explicitSequential.ambient where
  concept := explicitFiniteInverseLimitCompactness
  layer := ambient
  interface := ReverseMathlib.Standard.ExplicitFiniteInverseLimitCompactness
  description := "Ambient explicit sequential inverse-limit compactness: Finset fibers, \
    adjacent bonding maps, sections exist"

rm_statement_variant countableHall.oneSidedInjective.ambient where
  concept := countableHall
  layer := ambient
  interface := ReverseMathlib.Standard.CountableHall
  description := "Ambient one-sided countable Hall: ℕ-indexed Finset family with the \
    marriage condition admits an injective transversal (related to but not identical with \
    Simpson's perfect-matching variants)"

rm_external_ref rmzoo "WKL" exactAlias concept wkl
rm_external_ref simpson "I.10" sourceLocation concept wkl
rm_external_ref concordance "C085" importedCorrespondence concept wkl
rm_external_ref simpson "X.3.16" relatedVariant concept countableHall
rm_external_ref simpson "X.3.15" relatedVariant concept countableHall

end ReverseMathlib.Ports
