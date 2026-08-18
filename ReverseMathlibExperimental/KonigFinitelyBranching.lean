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

open OracleCode

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

/-- The least-bound characterization the computability layer decides bit by bit. -/
theorem levelBound_eq_iff (T : InternalFinitelyBranchingTree Ω) {i b : ℕ} :
    levelBound T i = b ↔
      BoundsLevel T.tree.1 i b ∧ ∀ b' < b, ¬ BoundsLevel T.tree.1 i b' := by
  constructor
  · rintro rfl
    exact ⟨levelBound_boundsLevel T i,
      fun b' hb' hcon => absurd (levelBound_le T hcon) (by omega)⟩
  · rintro ⟨hb, hmin⟩
    have h1 := levelBound_le T hb
    have h2 : ¬ levelBound T i < b := fun hlt => hmin _ hlt (levelBound_boundsLevel T i)
    omega

/-! ### The least level bound is computable from the jump of the tree

The failure of a candidate bound is witnessed by a single tree node, so it is
semidecidable in the tree alone: search the node codes for an entry at the position
reaching the candidate. Currying pins `(position, candidate)` into the searched code and
one jump query answers each failure question; the graph bit at `(i, b)` is then a pure
`findIdx` over the finite transcript of failure bits at candidates `0, …, b` — the first
non-failing candidate must be exactly `b`. The oracle is `jumpSet T.tree.1` and nothing
else, exactly the pinned graph-level statement. -/

open Classical in
/-- The failure test on `(pair (pair i b) junk, candidate c)`: `0` exactly when `c` is a
tree node witnessing that `b` fails to bound position `i`. The searched shape: the outer
argument arrives as `Nat.pair (Nat.pair i b) x` through the curry coding, and the test
reads only its first component. -/
private noncomputable def levelFailTest (S : Set ℕ) (q : ℕ) : ℕ :=
  if charFnTot S q.unpair.2 = 1 ∧
      q.unpair.1.unpair.1.unpair.1 < (decodeSeq q.unpair.2).length ∧
      q.unpair.1.unpair.1.unpair.2 ≤ (decodeSeq q.unpair.2).getD
        q.unpair.1.unpair.1.unpair.1 0
  then 0 else 1

private theorem levelFailTest_recursiveIn (S : Set ℕ) :
    Nat.RecursiveIn {charFn S} fun q => Part.some (levelFailTest S q) := by
  classical
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hSb : Nat.RecursiveIn {charFn S} fun e => Part.some (charFnTot S e) := by
    refine (Nat.RecursiveIn.oracle (O := {charFn S}) (charFn S) rfl).of_eq fun e => ?_
    rw [charFn_eq_coe]
    rfl
  have hbit := recursiveIn_comp_primrec hSb hsnd
  have hpair := recursiveIn_pair_total hbit (recursiveIn_of_primrec Primrec.id)
  -- pure post-processing of (membership bit, original input)
  have hpost : Primrec fun z : ℕ =>
      if z.unpair.1 = 1 ∧
          z.unpair.2.unpair.1.unpair.1.unpair.1 <
            (decodeSeq z.unpair.2.unpair.2).length ∧
          z.unpair.2.unpair.1.unpair.1.unpair.2 ≤
            (decodeSeq z.unpair.2.unpair.2).getD
              z.unpair.2.unpair.1.unpair.1.unpair.1 0
      then 0 else 1 := by
    have hq : Primrec fun z : ℕ => z.unpair.2 := hsnd
    have hi : Primrec fun z : ℕ =>
        z.unpair.2.unpair.1.unpair.1.unpair.1 :=
      hfst.comp (hfst.comp (hfst.comp hsnd))
    have hb : Primrec fun z : ℕ =>
        z.unpair.2.unpair.1.unpair.1.unpair.2 :=
      hsnd.comp (hfst.comp (hfst.comp hsnd))
    have hc : Primrec fun z : ℕ => z.unpair.2.unpair.2 := hsnd.comp hsnd
    have hlen : Primrec fun z : ℕ => (decodeSeq z.unpair.2.unpair.2).length :=
      primrec_seqLength.comp hc
    have hget : Primrec fun z : ℕ =>
        (decodeSeq z.unpair.2.unpair.2).getD
          z.unpair.2.unpair.1.unpair.1.unpair.1 0 :=
      Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet hc hi
    exact Primrec.ite
      ((PrimrecPred.and (Primrec.eq.comp hfst (Primrec.const 1))
        (PrimrecPred.and (Primrec.nat_lt.comp hi hlen)
          (Primrec.nat_le.comp hb hget))))
      (Primrec.const 0) (Primrec.const 1)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun q => ?_
  simp only [Nat.unpair_pair, id_eq, levelFailTest]

/-- **The graph-level reduction of the pin**: the least level-bound function's graph is
Turing reducible to the jump of the tree alone. One curry-coded jump query per failure
bit, a finite transcript at candidates `0, …, b`, and a pure `findIdx`. -/
theorem levelBoundGraph_le_jump (T : InternalFinitelyBranchingTree Ω) :
    levelBoundGraph T ≤ᵀ jumpSet T.tree.1 := by
  classical
  obtain ⟨e, he⟩ := exists_code.mp
    (Nat.RecursiveIn.rfind (levelFailTest_recursiveIn T.tree.1))
  -- one jump query decides each failure question
  have key : ∀ p : ℕ, (¬ BoundsLevel T.tree.1 p.unpair.1 p.unpair.2 ↔
      Encodable.encode (OracleCode.curry e p) ∈ jumpSet T.tree.1) := by
    intro p
    rw [mem_jumpSet_iff, Denumerable.ofNat_encode, ← charFn_eq_coe, eval_curry, he,
      Nat.rfind_dom]
    simp only [Part.map_eq_map, Part.map_some]
    constructor
    · intro hfail
      rw [BoundsLevel] at hfail
      push Not at hfail
      obtain ⟨c, hc, hlen, hge⟩ := hfail
      refine ⟨c, ?_, fun {m} _ => trivial⟩
      rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq, levelFailTest]
      simp only [Nat.unpair_pair]
      rw [if_pos ⟨by simp [charFnTot, hc], hlen, hge⟩]
    · rintro ⟨c, hc, -⟩ hb
      rw [Part.mem_some_iff] at hc
      have := hc.symm
      rw [levelFailTest] at this
      split at this
      · rename_i h
        simp only [Nat.unpair_pair] at h
        obtain ⟨hmem, hlen, hge⟩ := h
        have hcS : c ∈ T.tree.1 := by
          by_contra hno
          simp [charFnTot, hno] at hmem
        exact absurd (hb c hcS hlen) (by omega)
      · exact absurd this (by simp)
  -- the transcript of failure bits at candidates 0..b, then a pure findIdx
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hJb : Nat.RecursiveIn {charFn (jumpSet T.tree.1)} fun x => Part.some
      (charFnTot (jumpSet T.tree.1) x) := by
    refine (Nat.RecursiveIn.oracle (O := {charFn (jumpSet T.tree.1)})
      (charFn (jumpSet T.tree.1)) rfl).of_eq fun x => ?_
    rw [charFn_eq_coe]
    rfl
  have hquery : Primrec fun m : ℕ => Encodable.encode
      (OracleCode.curry e (Nat.pair m.unpair.1 m.unpair.2)) :=
    Primrec.encode.comp (primrec₂_curry.comp (_root_.Primrec.const e)
      (Primrec₂.comp (f := Nat.pair) Primrec₂.natPair hfst hsnd))
  have hfb : Nat.RecursiveIn {charFn (jumpSet T.tree.1)} fun m => Part.some
      (charFnTot (jumpSet T.tree.1) (Encodable.encode
        (OracleCode.curry e (Nat.pair m.unpair.1 m.unpair.2)))) :=
    recursiveIn_comp_primrec hJb hquery
  have htab := valueTable_recursiveIn_param
    (f := fun i b' => charFnTot (jumpSet T.tree.1) (Encodable.encode
      (OracleCode.curry e (Nat.pair i b')))) hfb
  have hib : Nat.RecursiveIn {charFn (jumpSet T.tree.1)} fun m => Part.some
      (Nat.pair m.unpair.1 (m.unpair.2 + 1)) :=
    recursiveIn_of_primrec (Primrec₂.comp (f := Nat.pair) Primrec₂.natPair hfst
      (Primrec.succ.comp hsnd))
  have htabm : Nat.RecursiveIn {charFn (jumpSet T.tree.1)} fun m => Part.some
      (valueTable (fun b' => charFnTot (jumpSet T.tree.1) (Encodable.encode
        (OracleCode.curry e (Nat.pair m.unpair.1 b')))) (m.unpair.2 + 1)) :=
    (recursiveIn_comp_total htab hib).of_eq fun m => by simp only [Nat.unpair_pair]
  have hpair := recursiveIn_pair_total htabm (recursiveIn_of_primrec Primrec.id)
  have hpost : Primrec fun z : ℕ =>
      if (decodeSeq z.unpair.1).findIdx (· == 0) = z.unpair.2.unpair.2
      then 1 else 0 := by
    have hidx : Primrec fun z : ℕ => (decodeSeq z.unpair.1).findIdx (· == 0) :=
      Primrec.list_findIdx (primrec_decodeSeq.comp hfst)
        (Primrec.beq.comp Primrec.snd (Primrec.const 0))
    exact Primrec.ite (Primrec.eq.comp hidx (hsnd.comp hsnd))
      (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun m => ?_
  simp only [Nat.unpair_pair, id_eq, decodeSeq_valueTable, charFn]
  -- the failure bit at (i, b') is 1 exactly when b' fails
  have hbit : ∀ i b' : ℕ, charFnTot (jumpSet T.tree.1) (Encodable.encode
      (OracleCode.curry e (Nat.pair i b'))) =
        if BoundsLevel T.tree.1 i b' then 0 else 1 := by
    intro i b'
    by_cases hbl : BoundsLevel T.tree.1 i b'
    · have : Encodable.encode (OracleCode.curry e (Nat.pair i b')) ∉
          jumpSet T.tree.1 := fun hmem =>
        ((key (Nat.pair i b')).mpr (by simpa using hmem)) (by simpa using hbl)
      simp [charFnTot, this, hbl]
    · have : Encodable.encode (OracleCode.curry e (Nat.pair i b')) ∈
          jumpSet T.tree.1 := by
        have := (key (Nat.pair i b')).mp (by simpa using hbl)
        simpa using this
      simp [charFnTot, this, hbl]
  -- the first non-failing candidate is the least bound
  set i := m.unpair.1
  set b := m.unpair.2
  have hlist : (List.range (b + 1)).map (fun b' => charFnTot (jumpSet T.tree.1)
      (Encodable.encode (OracleCode.curry e (Nat.pair i b')))) =
      (List.range (b + 1)).map (fun b' => if BoundsLevel T.tree.1 i b' then 0 else 1) :=
    List.map_congr_left fun b' _ => hbit i b'
  rw [hlist]
  by_cases hg : levelBound T i = b
  · have hchar := (levelBound_eq_iff T).mp hg
    have hfind : ((List.range (b + 1)).map
        (fun b' => if BoundsLevel T.tree.1 i b' then 0 else 1)).findIdx (· == 0) = b := by
      have hblen : b < ((List.range (b + 1)).map
          (fun b' => if BoundsLevel T.tree.1 i b' then 0 else 1)).length := by
        simp
      rw [List.findIdx_eq hblen]
      constructor
      · simp only [List.getElem_map, List.getElem_range]
        simp [hchar.1]
      · intro j hj
        simp only [List.getElem_map, List.getElem_range]
        simp [hchar.2 j hj]
    rw [if_pos hfind, if_pos (show m ∈ levelBoundGraph T from hg)]
  · have hfind : ((List.range (b + 1)).map
        (fun b' => if BoundsLevel T.tree.1 i b' then 0 else 1)).findIdx (· == 0) ≠ b := by
      intro hcon
      have hblen : b < ((List.range (b + 1)).map
          (fun b' => if BoundsLevel T.tree.1 i b' then 0 else 1)).length := by
        simp
      rw [List.findIdx_eq hblen] at hcon
      obtain ⟨hb0, hmin⟩ := hcon
      simp only [List.getElem_map, List.getElem_range] at hb0 hmin
      refine hg ((levelBound_eq_iff T).mpr ⟨?_, fun b' hb' => ?_⟩)
      · by_contra hno
        simp [hno] at hb0
      · have := hmin b' hb'
        by_contra hyes
        simp [hyes] at this
    rw [if_neg hfind, if_neg (show m ∉ levelBoundGraph T from hg)]

/-! ### Packaging: jump closure gives full finitely-branching Kőnig

The least level bound is internal by one `levelBoundGraph_le_jump` reduction below the
jump of the tree; packaging it as a graph-coded internal function turns the finitely
branching tree into an explicitly bounded one, and Slice A does the rest. -/

/-- **Jump closure gives full finitely-branching Kőnig** over the Turing-ideal closure
conditions — the forward direction of the slice. -/
theorem finitelyBranchingKonigAt_of_jumpClosedAt {Ω : OmegaPart}
    (hΩ : IsTuringIdeal Ω) (hJ : JumpClosedAt Ω) : FinitelyBranchingKonigAt Ω := by
  intro T hlev
  have hgraph : levelBoundGraph T ∈ Ω :=
    hΩ.mem_of_reducible (hJ T.tree) (levelBoundGraph_le_jump T)
  exact boundedKonigAt_of_jumpClosedAt hΩ hJ
    { tree := T.tree
      bound :=
        ⟨⟨levelBoundGraph T, hgraph⟩,
         fun i => ⟨levelBound T i, (isGraphOf_levelBoundGraph T i _).mpr rfl⟩,
         fun i y y' hy hy' => ((isGraphOf_levelBoundGraph T i y).mp hy).symm.trans
           ((isGraphOf_levelBoundGraph T i y').mp hy')⟩
      entry_lt_bound := fun c hc i b hi hb => by
        have hlb : levelBound T i = b := (isGraphOf_levelBoundGraph T i b).mp hb
        exact hlb ▸ levelBound_boundsLevel T i c hc hi
      prefix_closed := T.prefix_closed } hlev

/-! ### The reversal, stage one: the injection tree

The route (user-pinned): `FinitelyBranchingKonigAt → InjectionRangeExistenceAt →
JumpClosedAt`, with the intermediate implication owned by
`injectionRangeExistenceAt_of_finitelyBranchingKonigAt` (this construction) and the
final theorem a short composition through fact 7's direction; the intermediate is proof
architecture, never a registered fact.

A node guesses, for each position `i` below its length, whether `i` is a value of the
injection: entry `0` means "no witness below the node's length", entry `w + 1` names the
witness by the **single query** `f.MapsTo w i` — never an unbounded range search. The
zero clause is falsifiable at deeper levels, so along a path the guesses become truth:
that is `path_determines_range`. -/

/-- Membership of a node in the injection tree: each nonzero entry names its witness by
one graph query, and each zero entry asserts no witness below the node's length —
bounded quantification only. -/
def InjectionNodeOk {Ω : OmegaPart} (f : InternalFunction Ω) (c : ℕ) : Prop :=
  ∀ i < (decodeSeq c).length,
    (∀ w, (decodeSeq c).getD i 0 = w + 1 → f.MapsTo w i) ∧
    ((decodeSeq c).getD i 0 = 0 → ∀ w < (decodeSeq c).length, ¬ f.MapsTo w i)

/-- The injection tree, as a set of sequence codes. -/
def injectionTreeSet {Ω : OmegaPart} (f : InternalFunction Ω) : Set ℕ :=
  {c | InjectionNodeOk f c}

theorem injectionTree_prefix_closed {Ω : OmegaPart} (f : InternalFunction Ω) :
    ∀ c ∈ injectionTreeSet f, ∀ k, seqCode ((decodeSeq c).take k) ∈ injectionTreeSet f := by
  intro c hc k i hi
  rw [decodeSeq_seqCode, List.length_take] at hi
  have hilen : i < (decodeSeq c).length := lt_of_lt_of_le hi (by omega)
  have hgd : (decodeSeq (seqCode ((decodeSeq c).take k))).getD i 0 =
      (decodeSeq c).getD i 0 := by
    rw [decodeSeq_seqCode, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos (show i < k by omega), ← List.getD_eq_getElem?_getD]
  obtain ⟨h1, h2⟩ := hc i hilen
  refine ⟨fun w hw => h1 w (by rwa [hgd] at hw), fun h0 w hw hmap => ?_⟩
  rw [decodeSeq_seqCode, List.length_take] at hw
  exact h2 (by rwa [hgd] at h0) w (by omega) hmap

/-- **Injectivity establishes levelwise boundedness**: a position has at most one
witness, so tree entries there lie in `{0, w + 1}`. -/
theorem injectionTree_levelwise_bounded {Ω : OmegaPart} (f : InternalFunction Ω)
    (hf : f.IsInjective) (i : ℕ) :
    ∃ b, ∀ c ∈ injectionTreeSet f, i < (decodeSeq c).length →
      (decodeSeq c).getD i 0 < b := by
  classical
  by_cases hw : ∃ w, f.MapsTo w i
  · obtain ⟨w, hwmap⟩ := hw
    refine ⟨w + 2, fun c hc hi => ?_⟩
    obtain ⟨h1, -⟩ := hc i hi
    match hv : (decodeSeq c).getD i 0 with
    | 0 => omega
    | u + 1 =>
      have := hf u w i (h1 u hv) hwmap
      omega
  · refine ⟨1, fun c hc hi => ?_⟩
    obtain ⟨h1, -⟩ := hc i hi
    match hv : (decodeSeq c).getD i 0 with
    | 0 => omega
    | u + 1 => exact absurd ⟨u, h1 u hv⟩ hw

/-- Reading a function's values off positions of its own range-indexed table (local
copy of the Slice A helper, which is private there). -/
private theorem map_range_getD' {α : Type*} (f : ℕ → α) {w v : ℕ} (hv : v < w)
    (d : α) : ((List.range w).map f).getD v d = f v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
  rfl

open Classical in
/-- The truthful stage-`n` node: at position `i`, the least witness below `n` if one
exists, else zero. -/
private noncomputable def truthNode {Ω : OmegaPart} (f : InternalFunction Ω)
    (n : ℕ) : ℕ :=
  seqCode ((List.range n).map fun i =>
    if h : ∃ w < n, f.MapsTo w i then sInf {w | f.MapsTo w i} + 1 else 0)

/-- **Prefix closure and bounded membership establish infinitude**: the truthful stage
node lives at every level. -/
theorem injectionTree_hasNodeAtEveryLevel {Ω : OmegaPart} (f : InternalFunction Ω) :
    HasNodeAtEveryLevel (injectionTreeSet f) := by
  classical
  intro n
  refine ⟨truthNode f n, ?_, by simp [truthNode]⟩
  intro i hi
  rw [truthNode, decodeSeq_seqCode] at hi ⊢
  simp only [List.length_map, List.length_range] at hi
  have hgd : ((List.range n).map fun j =>
      if h : ∃ w < n, f.MapsTo w j then sInf {w | f.MapsTo w j} + 1 else 0).getD i 0 =
      if h : ∃ w < n, f.MapsTo w i then sInf {w | f.MapsTo w i} + 1 else 0 :=
    map_range_getD' _ hi 0
  constructor
  · intro w hwv
    rw [hgd] at hwv
    split at hwv
    · rename_i h
      obtain ⟨w0, -, hw0⟩ := h
      have hmem : sInf {w | f.MapsTo w i} ∈ {w | f.MapsTo w i} := Nat.sInf_mem ⟨w0, hw0⟩
      have : w = sInf {w | f.MapsTo w i} := by omega
      exact this ▸ hmem
    · omega
  · intro h0 w hwn hmap
    rw [hgd] at h0
    split at h0
    · omega
    · rename_i h
      simp only [List.length_map, List.length_range] at hwn
      exact h ⟨w, hwn, hmap⟩

/-- **Path correctness establishes the range characterization**: along a path through
the injection tree, a position holds zero exactly when it is not a value of the
injection — a real witness eventually rules zero out at sufficient depth, while a
positive path value directly supplies its witness. -/
theorem path_determines_range {Ω : OmegaPart} (f : InternalFunction Ω)
    {p : InternalFunction Ω} (hp : IsBoundedPathThrough p (injectionTreeSet f))
    (v : ℕ) : ¬ p.MapsTo v 0 ↔ ∃ m, f.MapsTo m v := by
  constructor
  · intro h0
    obtain ⟨u, hu⟩ := p.total v
    rcases u with _ | w
    · exact absurd hu h0
    · obtain ⟨c, hcT, hclen, hagree⟩ := hp (v + 1)
      have hgd : (decodeSeq c).getD v 0 = w + 1 := hagree v (by omega) _ hu
      exact ⟨w, (hcT v (by omega)).1 w hgd⟩
  · rintro ⟨w, hw⟩ hp0
    obtain ⟨c, hcT, hclen, hagree⟩ := hp (max w v + 1)
    have hgd : (decodeSeq c).getD v 0 = 0 := hagree v (by omega) _ hp0
    exact (hcT v (by omega)).2 hgd w (by omega) hw

end ReverseMathlib.Omega
