import ReverseMathlib.Omega.KonigLeftmostPath

/-!
Slice B scratch (issue #50): full finitely-branching Kőnig at a second-order part, and
the forward direction from jump closure.

The concept is the levelwise-bound **property** (Hirst thesis Theorem 1.3: for every
position there exists a bound on the entries there), never a supplied bound function —
that supplied-data presentation is the explicitly bounded variant already registered
with the fourth fact. The forward direction computes the **least** level bound from the
jump of the tree (graph-level reduction, internal packaging by ideal closure
separately), turning the finitely-branching tree into an explicitly bounded one and
reusing all of Slice A.

Nothing here enters the spine until the whole slice is green.

A plain `lake build` does not compile this file: the experimental root does not
import it, and CI will not catch a break here. Build it by name:

  lake build ReverseMathlibExperimental.KonigFinitelyBranching
-/

namespace ReverseMathlib.Omega

variable {Ω : OmegaPart}

/-- An internally presented finitely branching tree: an internal set of sequence codes,
prefix-closed through the canonical coding, whose entries at each position are bounded —
a **property** of the bare tree (levelwise: for every position some bound exists), never
supplied data. This is the ACA-level presentation; the explicitly bounded presentation
(`InternalBoundedTree`) carries its bound as a graph-coded internal function and is a
different, weaker concept. -/
structure InternalFinitelyBranchingTree (Ω : OmegaPart) where
  /-- The tree: an internal set of sequence codes. -/
  tree : Ω.InternalSet
  /-- The tree is closed under truncation of decoded sequences. -/
  prefix_closed : ∀ c ∈ tree.1, ∀ k, seqCode ((decodeSeq c).take k) ∈ tree.1
  /-- Levelwise boundedness, as a property: at each position some strict bound exists on
  the decoded entries there. -/
  levelwise_bounded : ∀ i, ∃ b, ∀ c ∈ tree.1, i < (decodeSeq c).length →
    (decodeSeq c).getD i 0 < b

/-- Full (merely) finitely-branching Kőnig at a second-order part: every internally
presented finitely branching tree with a node at every level has an internal path. The
bound is a property, not data — this is the ACA-level principle, deliberately distinct
from `BoundedKonigAt`. -/
def FinitelyBranchingKonigAt (Ω : OmegaPart) : Prop :=
  ∀ T : InternalFinitelyBranchingTree Ω, HasNodeAtEveryLevel T.tree.1 →
    ∃ p : InternalFunction Ω, IsBoundedPathThrough p T.tree.1

/-! ### The least level bound

`Nat.sInf` is total, so the least bound is a definition; every lemma below carries the
witness from `levelwise_bounded`, so the empty-set fallback value never acquires
semantic meaning. -/

/-- `b` strictly bounds every decoded entry at position `i` of a tree node. -/
def BoundsLevel (S : Set ℕ) (i b : ℕ) : Prop :=
  ∀ c ∈ S, i < (decodeSeq c).length → (decodeSeq c).getD i 0 < b

/-- The least strict bound at position `i` — the value the forward direction computes
from the jump. -/
noncomputable def levelBound (T : InternalFinitelyBranchingTree Ω) (i : ℕ) : ℕ :=
  sInf {b | BoundsLevel T.tree.1 i b}

theorem levelBound_boundsLevel (T : InternalFinitelyBranchingTree Ω) (i : ℕ) :
    BoundsLevel T.tree.1 i (levelBound T i) :=
  Nat.sInf_mem (T.levelwise_bounded i)

theorem levelBound_le (T : InternalFinitelyBranchingTree Ω) {i b : ℕ}
    (hb : BoundsLevel T.tree.1 i b) : levelBound T i ≤ b :=
  Nat.sInf_le hb

/-- Below the least bound, some node entry reaches at least the candidate: the negative
side, in the witness form the computability layer decides. -/
theorem exists_entry_ge_of_lt_levelBound (T : InternalFinitelyBranchingTree Ω)
    {i b : ℕ} (hb : b < levelBound T i) :
    ∃ c ∈ T.tree.1, i < (decodeSeq c).length ∧ b ≤ (decodeSeq c).getD i 0 := by
  by_contra hcon
  push Not at hcon
  have hb' : BoundsLevel T.tree.1 i b := fun c hc hi => by
    have := hcon c hc hi
    omega
  exact absurd (levelBound_le T hb') (by omega)

/-- The graph of the least level-bound function, as `Nat.pair` codes. -/
def levelBoundGraph (T : InternalFinitelyBranchingTree Ω) : Set ℕ :=
  {m | levelBound T m.unpair.1 = m.unpair.2}

theorem isGraphOf_levelBoundGraph (T : InternalFinitelyBranchingTree Ω) :
    IsGraphOf (levelBoundGraph T) (levelBound T) := fun x y => by
  simp [levelBoundGraph, Nat.unpair_pair, Set.mem_setOf_eq]

end ReverseMathlib.Omega
