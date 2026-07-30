/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Graph

/-!
# Internal binary trees and weak Kőnig's lemma at a second-order part (issue #22, slice 2)

An internal binary tree is an **internal set of sequence codes** (the canonical `seqCode`
coding); binary-valuedness and prefix closure are ordinary properties of that internal set.
A path is an internal set of bit-`1` positions; matching the tree is stated relationally
against decoded prefixes — no classical `if` and no `InternalFunction.eval` appears in any
statement here, so the capability's statement closure stays choice-free by construction.

`WeakKonigAt Ω` deliberately carries **no base-theory premise**: the RCAω/Turing-ideal
context enters through the registered semantic context of a certificate, never through the
capability statement itself.
-/

namespace ReverseMathlib.Omega

/-- A binary tree code: every member decodes to a bit sequence, and the set is closed under
truncation of decoded sequences (prefix closure through the canonical coding). -/
def IsBinaryTreeCode (T : Set ℕ) : Prop :=
  (∀ c ∈ T, IsBitSeqCode c) ∧ ∀ c ∈ T, ∀ k, seqCode ((decodeSeq c).take k) ∈ T

/-- The tree has a node at every level. -/
def HasNodeAtEveryLevel (T : Set ℕ) : Prop :=
  ∀ n, ∃ c ∈ T, (decodeSeq c).length = n

/-- `P` (a set of bit-`1` positions) is a path through `T`: for every length, some tree node
of that length agrees with `P` entrywise. Stated relationally — no selection, no `if`. -/
def IsBinaryPathThrough (P T : Set ℕ) : Prop :=
  ∀ n, ∃ c ∈ T, (decodeSeq c).length = n ∧
    ∀ i < n, ((decodeSeq c).getD i 0 = 1 ↔ i ∈ P)

/-- Weak Kőnig's lemma at a second-order part: every internal binary tree with a node at
every level has an internal path. The Turing-ideal presentation of the ω-model layer;
no base-theory premise inside the capability. -/
def WeakKonigAt (Ω : OmegaPart) : Prop :=
  ∀ T : Ω.InternalSet, IsBinaryTreeCode T.1 → HasNodeAtEveryLevel T.1 →
    ∃ P : Ω.InternalSet, IsBinaryPathThrough P.1 T.1

end ReverseMathlib.Omega
