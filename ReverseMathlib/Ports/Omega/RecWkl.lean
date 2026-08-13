/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Omega.KleeneTree
import ReverseMathlib.Ports.Omega.Catalog

/-!
# The first certified separation: RCA₀-core ⊭ω WKL (tranche 4)

The **atomic registration** of the first typed semantic nonimplication: the base-capability
concept and variant giving the separation a typed lhs, the nonimplication fact, the exact
countermodel certificate (visibly the named countermodel `recursivePart` with the named
Kleene-tree separation theorem, pinned by a dependency gate in `scripts/MetaSmoke.lean`),
and its certification against `rca0.turingIdealOmega`.

The verdict stays precisely scoped: a kernel-checked **model-class separation** over the
registered Turing-ideal context — WKLω fails in some Turing ideal satisfying the RCA₀
closure core (namely REC) — with the identification of Turing ideals with RCA₀'s ω-models
literature-backed and backend adequacy pending. This is **never** rendered as, and never
promoted to, a checked `RCA₀ ⊬ WKL` turnstile theorem; that claim would need the syntactic
layer, which remains empty.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib.Omega

rm_concept rca0Core where
  statement := "Not a mathematical principle but a base capability: a second-order part is \
    an RCA₀ core when it is nonempty, closed downward under Turing reducibility, and \
    closed under recursive join — the Turing-ideal closure conditions used for the \
    repository's RCA₀ ω context"
  description := "The second-order core of RCA₀ at a fixed first-order part: nonemptiness, \
    downward Δ⁰₁ (Turing) closure, and closure under recursive join — the Turing-ideal \
    closure conditions used as the repository's RCA₀ ω context. A base-capability \
    concept: it names those closure conditions so ω-scope separations have an honest \
    typed lhs; it is not a theorem-strength concept and carries no external crosswalk"

rm_statement_variant rca0Core.turingIdealClosure.turingIdealOmega where
  concept := rca0Core
  layer := turingIdealOmega
  interface := ReverseMathlib.Omega.IsTuringIdeal
  description := "The RCA₀ second-order core at a second-order part, Turing-ideal \
    presentation: the part is nonempty, downward closed under set-based Turing \
    reducibility, and closed under the recursive join — the same closure conditions the \
    semantic context rca0.turingIdealOmega imposes on every model, packaged as a \
    capability so that separations have a typed lhs"

/-- **The countermodel certificate**: REC — the recursive-set Turing ideal — satisfies the
RCA₀ closure core and falsifies WKLω. Visibly the named countermodel `recursivePart` with
the named separation theorem `not_weakKonigAt_recursivePart` and nothing else; the
dependency gate in `scripts/MetaSmoke.lean` requires this proof to reach the Kleene-tree
route, so registration preserves the construction artifact. -/
theorem rec_countermodel_weakKonig :
    Meta.SemanticNonimplicationCertificate IsTuringIdeal IsTuringIdeal WeakKonigAt :=
  ⟨⟨recursivePart, recursivePart_isTuringIdeal, recursivePart_isTuringIdeal,
    not_weakKonigAt_recursivePart⟩⟩

rm_fact rca0CoreWklOmega nonImplication where
  base := rca0
  scope := omegaModels
  lhs := [rca0Core.turingIdealClosure.turingIdealOmega]
  rhs := [wkl.binaryTree.turingIdealOmega]
  note := "The first certified separation leaf: over the Turing-ideal ω layer, the RCA₀ \
    closure core does not force WKL — witnessed by the explicit countermodel REC through \
    the bounded-computation Kleene tree (Kleene, Recursive functions and intuitionistic \
    mathematics, Proc. ICM Cambridge 1950; cf. [Sim09] VIII.2 — citation claimed, \
    unverified against a pinned snapshot). A model-class separation only: never a checked \
    RCA₀ ⊬ WKL turnstile theorem"

revmath_certify_fact rca0CoreWklOmega where
  context := rca0.turingIdealOmega
  via := ReverseMathlib.Ports.rec_countermodel_weakKonig
  note := "The named countermodel REC with the named separation theorem \
    not_weakKonigAt_recursivePart; the Kleene-tree route and this certificate's \
    composition are pinned by dependency gates in scripts/MetaSmoke.lean"

end ReverseMathlib.Ports
