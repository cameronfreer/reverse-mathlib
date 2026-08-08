/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Tree

/-!
# Internal explicitly bounded trees and bounded Kőnig at a second-order part
(issue #39, slice 2)

The **explicitly bounded** Kőnig presentation: a tree of sequence codes together with a
**supplied** coordinatewise bound, packaged as a graph-coded internal function — the ω-model
form of the ambient `EntriesBounded` contract (`ReverseMathlib/Standard/Trees.lean`). The
bound is data, exactly as EFILC's fiber enumerations are data; a tree that merely *happens*
to be finitely branching carries no such certificate, and that unrestricted principle (full
Kőnig, ACA-level) is deliberately **not** what is stated here — see the concept note in
`ReverseMathlib/Ports/Catalog.lean` keeping the two apart.

A path through a bounded tree chooses a natural number at every position, so it is a
graph-coded internal function rather than a set of bit positions; matching the tree is
stated relationally against decoded prefixes. No classical `if` and no
`InternalFunction.eval` appears in any statement here (see the statement-burden gate in
`scripts/MetaSmoke.lean`).

`BoundedKonigAt Ω` carries no base-theory premise, exactly like `WeakKonigAt`.
-/

namespace ReverseMathlib.Omega

/-- An internally presented explicitly bounded tree: an internal set of sequence codes that
is prefix-closed through the canonical coding, together with a graph-coded internal bound
function certifying, coordinatewise, that every decoded entry at position `i` lies strictly
below the bound at `i`. The bound is supplied data — this is never a finite-branching
*property* of the bare tree. -/
structure InternalBoundedTree (Ω : OmegaPart) where
  /-- The tree: an internal set of sequence codes. -/
  tree : Ω.InternalSet
  /-- The explicit coordinatewise bound, as a graph-coded internal function. -/
  bound : InternalFunction Ω
  /-- Every decoded entry lies strictly below the supplied bound at its position. -/
  entry_lt_bound : ∀ c ∈ tree.1, ∀ i b, i < (decodeSeq c).length →
    bound.MapsTo i b → (decodeSeq c).getD i 0 < b
  /-- The tree is closed under truncation of decoded sequences. -/
  prefix_closed : ∀ c ∈ tree.1, ∀ k, seqCode ((decodeSeq c).take k) ∈ tree.1

/-- `p` (a graph-coded choice of one natural number per position) is a path through `T`:
for every length, some tree node of that length agrees with `p` entrywise. Stated
relationally — no selection, no `if`, no `eval`. -/
def IsBoundedPathThrough {Ω : OmegaPart} (p : InternalFunction Ω) (T : Set ℕ) : Prop :=
  ∀ n, ∃ c ∈ T, (decodeSeq c).length = n ∧
    ∀ i < n, ∀ v, p.MapsTo i v → (decodeSeq c).getD i 0 = v

/-- Explicitly bounded Kőnig's lemma at a second-order part: every internally presented
explicitly bounded tree with a node at every level has an internal path. The Turing-ideal
presentation of the ω-model layer; no base-theory premise inside the capability. -/
def BoundedKonigAt (Ω : OmegaPart) : Prop :=
  ∀ T : InternalBoundedTree Ω, HasNodeAtEveryLevel T.tree.1 →
    ∃ p : InternalFunction Ω, IsBoundedPathThrough p T.tree.1

end ReverseMathlib.Omega
