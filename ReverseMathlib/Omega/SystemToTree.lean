/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.BitCoding
import ReverseMathlib.Omega.InverseSystem

/-!
# `systemToTree`: compiling an inverse system to a binary tree (issue #22, slice 3)

The construction, its specification verifier, the table-driven implementation, the finite
oracle transcripts, and the reduction `systemTreeSet F ≤ᵀ systemOracle F`.

The computability argument is in the normal form *finite oracle transcript, then pure
verifier*. All unbounded search is confined to the two lookup **channels** — fiber lookup
and bonding lookup — used while materializing the finite transcripts; each transcript makes
finitely many, input-dependent invocations of those channels (roughly one per fiber-table
row and one per bond-table entry). Everything after transcript construction is pure
primitive-recursive computation.

The presentation-local table machinery (`tableRow`, `tupleOkT`, `tableTuples`, …) belongs
to this module: it is a way of computing *this* verifier, not general coding API.
-/

namespace ReverseMathlib.Omega

/-! ### `systemToTree`: compiling an inverse system to a binary tree

Chunk widths are **deliberately inefficient**: the level-`k` chunk has width equal to the
level-`k` fiber-list length `m`, so the width is at least `1` automatically for nonempty
fibers and `m ≤ 2 ^ m` leaves room to encode every index — there is no
reverse-mathematical value in optimizing to `⌈log₂ m⌉`, while logarithmic arithmetic would
complicate the primitive-recursive proofs. Tree membership is **extensional**: a
bit-sequence code whose decoding is a prefix of the encoding of some finite coherent
tuple — prefix closure is immediate, and incomplete chunks are treated uniformly as
genuine nodes. Everything is relational: fiber lists enter through `MapsTo`, never through
evaluation. -/

/-- Coherence of a level-`k` chosen element with the previous level's element (`none` at
the root): the bonding map sends the new element down to the previous one. -/
def BondOk {Ω : OmegaPart} (F : InternalInverseSystem Ω) (k : ℕ) :
    Option ℕ → ℕ → Prop
  | none, _ => True
  | some x, y => F.bonding.MapsTo (Nat.pair (k - 1) y) x

/-- Relational chunk encoding of a coherent **`j`-chunk** tuple from level `k` upward,
threading the previously chosen element for the coherence check. The level-`k` chunk is
`bitListOfIndex (fiber-list length) idx` for the chosen index `idx`; the chunk count makes
the bounded-witness normalization stateable. -/
inductive CoherentEncoding {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ℕ → Option ℕ → ℕ → List ℕ → Prop
  /-- The empty tuple encodes to no bits, at any level. -/
  | nil (k : ℕ) (prev : Option ℕ) : CoherentEncoding F k prev 0 []
  /-- Choose index `idx` in the level-`k` fiber, coherent with the previous element, and
  continue upward. -/
  | cons {k : ℕ} {prev : Option ℕ} {fc idx j : ℕ} {rest : List ℕ} :
      F.fibers.MapsTo k fc →
      idx < (decodeSeq fc).length →
      BondOk F k prev ((decodeSeq fc).getD idx 0) →
      CoherentEncoding F (k + 1) (some ((decodeSeq fc).getD idx 0)) j rest →
      CoherentEncoding F k prev (j + 1) (bitListOfIndex (decodeSeq fc).length idx ++ rest)

/-- Layer 1 (raw): the compiled tree — bit-sequence codes whose decoding is a prefix of
the encoding of some finite coherent tuple. -/
def systemTreeSet {Ω : OmegaPart} (F : InternalInverseSystem Ω) : Set ℕ :=
  {c | IsBitSeqCode c ∧
    ∃ j full, CoherentEncoding F 0 none j full ∧ decodeSeq c <+: full}

/-- The compiled tree is a binary tree code: bit content by definition; prefix closure is
immediate from the extensional prefix formulation — incomplete chunks are nodes. -/
theorem isBinaryTreeCode_systemTreeSet {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    IsBinaryTreeCode (systemTreeSet F) := by
  constructor
  · exact fun c hc => hc.1
  · rintro c ⟨hbits, j, full, henc, hpre⟩ k
    refine ⟨?_, j, full, henc, ?_⟩
    · intro x hx
      rw [decodeSeq_seqCode] at hx
      exact hbits x (List.mem_of_mem_take hx)
    · rw [decodeSeq_seqCode]
      exact (List.take_prefix k _).trans hpre

/-- Every chunk has positive width (fiber nonemptiness), so a `j`-chunk encoding has at
least `j` bits. -/
theorem CoherentEncoding.le_length {Ω : OmegaPart} {F : InternalInverseSystem Ω}
    {k : ℕ} {prev : Option ℕ} {j : ℕ} {full : List ℕ}
    (h : CoherentEncoding F k prev j full) : j ≤ full.length := by
  induction h with
  | nil => simp
  | cons hfc hidx _ _ ih =>
    simp only [List.length_append, bitListOfIndex_length]
    omega

/-- Truncation to the first `m` chunks preserves coherence and yields a prefix. -/
theorem CoherentEncoding.truncate {Ω : OmegaPart} {F : InternalInverseSystem Ω}
    {k : ℕ} {prev : Option ℕ} {j : ℕ} {full : List ℕ}
    (h : CoherentEncoding F k prev j full) :
    ∀ m ≤ j, ∃ full', CoherentEncoding F k prev m full' ∧ full' <+: full := by
  induction h with
  | nil =>
    intro m hm
    obtain rfl : m = 0 := by omega
    exact ⟨[], .nil _ _, List.prefix_refl _⟩
  | cons hfc hidx hbond _ ih =>
    intro m hm
    match m with
    | 0 => exact ⟨[], .nil _ _, List.nil_prefix⟩
    | m + 1 =>
      obtain ⟨full', henc', hpre'⟩ := ih m (by omega)
      obtain ⟨t, ht⟩ := hpre'
      exact ⟨_, .cons hfc hidx hbond henc', ⟨t, by rw [List.append_assoc, ht]⟩⟩

/-- **Bounded-witness normalization**: a bit string of length `L` in the tree is already a
prefix of a coherent encoding using at most `L` chunks — the lemma that converts the
existential specification into finite relative search (tuple length ≤ `L`, coordinates over
explicit finite fibers, finitely many bonding checks). -/
theorem systemTreeSet_bounded_witness {Ω : OmegaPart} {F : InternalInverseSystem Ω}
    {c : ℕ} (hc : c ∈ systemTreeSet F) :
    ∃ j full, j ≤ (decodeSeq c).length ∧ CoherentEncoding F 0 none j full ∧
      decodeSeq c <+: full := by
  obtain ⟨hbits, j, full, henc, hpre⟩ := hc
  by_cases hj : j ≤ (decodeSeq c).length
  · exact ⟨j, full, hj, henc, hpre⟩
  · obtain ⟨full', henc', hpre'⟩ := henc.truncate (decodeSeq c).length (by omega)
    exact ⟨_, full', le_refl _, henc',
      List.prefix_of_prefix_length_le hpre hpre' henc'.le_length⟩

/-- Every coherent encoding is a bit list (chunks are `bitListOfIndex` blocks). -/
theorem CoherentEncoding.mem_le_one {Ω : OmegaPart} {F : InternalInverseSystem Ω}
    {k : ℕ} {prev : Option ℕ} {j : ℕ} {full : List ℕ}
    (h : CoherentEncoding F k prev j full) : ∀ x ∈ full, x ≤ 1 := by
  induction h with
  | nil => simp
  | cons hfc hidx _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [bitListOfIndex, List.mem_map] at hx
      obtain ⟨j', -, rfl⟩ := hx
      split <;> omega
    · exact ih x hx

/-- **Top-parameterized downward completion**: a chosen member of the level-`n` fiber,
together with any coherent continuation above it, extends to a full coherent encoding from
level `0`. Induction pushes the element down through the bonding function — no
surjectivity of bonding maps is ever assumed (extending an arbitrary lower chain upward
would require exactly that). -/
theorem exists_coherentEncoding_of_top {Ω : OmegaPart} {F : InternalInverseSystem Ω} :
    ∀ n fc x, F.fibers.MapsTo n fc → x ∈ decodeSeq fc →
      ∀ j rest, CoherentEncoding F (n + 1) (some x) j rest →
        ∃ m full, m = n + 1 + j ∧ CoherentEncoding F 0 none m full := by
  intro n
  induction n with
  | zero =>
    intro fc x hfc hx j rest hrest
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hx
    have hval : (decodeSeq fc).getD i 0 = x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hgi, Option.getD_some]
    refine ⟨j + 1, bitListOfIndex (decodeSeq fc).length i ++ rest, by omega, ?_⟩
    refine CoherentEncoding.cons hfc hi trivial ?_
    rw [hval]
    exact hrest
  | succ n ih =>
    intro fc x hfc hx j rest hrest
    -- push x down through the bonding function; place the image in the level-n fiber
    obtain ⟨y, hy⟩ := F.bonding.total (Nat.pair n x)
    obtain ⟨fc', hfc'⟩ := F.fibers.total n
    have hymem : y ∈ decodeSeq fc' := F.bonding_mem n fc fc' x y hfc hfc' hx hy
    -- the level-(n+1) chunk for x, continuing into rest
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hx
    have hval : (decodeSeq fc).getD i 0 = x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hgi, Option.getD_some]
    have hrest' : CoherentEncoding F (n + 1) (some y) (j + 1)
        (bitListOfIndex (decodeSeq fc).length i ++ rest) := by
      refine CoherentEncoding.cons hfc hi ?_ ?_
      · change F.bonding.MapsTo (Nat.pair n ((decodeSeq fc).getD i 0)) y
        rwa [hval]
      · rw [hval]
        exact hrest
    obtain ⟨m, full, hm, henc⟩ := ih fc' y hfc' hymem (j + 1) _ hrest'
    exact ⟨m, full, by omega, henc⟩

/-- The compiled tree has a node at every bit length: choose a top element proof-locally
from fiber `L - 1`, complete downward, and take the first `L` encoded bits. -/
theorem hasNodeAtEveryLevel_systemTreeSet {Ω : OmegaPart}
    (F : InternalInverseSystem Ω) : HasNodeAtEveryLevel (systemTreeSet F) := by
  intro L
  match L with
  | 0 =>
    refine ⟨seqCode [], ⟨?_, 0, [], .nil _ _, by rw [decodeSeq_seqCode]⟩, ?_⟩
    · intro x hx
      rw [decodeSeq_seqCode] at hx
      simp at hx
    · rw [decodeSeq_seqCode]
      rfl
  | L + 1 =>
    obtain ⟨fc, hfc⟩ := F.fibers.total L
    have hne := F.fiber_nonempty L fc hfc
    have hlen : 0 < (decodeSeq fc).length := List.length_pos_iff.mpr hne
    have hx : (decodeSeq fc).getD 0 0 ∈ decodeSeq fc := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      exact List.getElem_mem hlen
    obtain ⟨m, full, hm, henc⟩ :=
      exists_coherentEncoding_of_top L fc _ hfc hx 0 [] (.nil _ _)
    have hLle : L + 1 ≤ full.length := by
      have := henc.le_length
      omega
    refine ⟨seqCode (full.take (L + 1)), ⟨?_, m, full, henc, ?_⟩, ?_⟩
    · intro x hx'
      rw [decodeSeq_seqCode] at hx'
      exact henc.mem_le_one x (List.mem_of_mem_take hx')
    · rw [decodeSeq_seqCode]
      exact List.take_prefix _ _
    · rw [decodeSeq_seqCode, List.length_take]
      omega

/-! ### `systemToTree` layer 2, stage 1: oracle-relative lookups

The join of the fiber and bonding graphs is the single oracle. These two lookups are the
**only unbounded-search channels** in the whole reduction: each is a terminating search for
a uniquely coded graph value, and the transcripts below invoke them finitely many times,
input-dependently. Everything after transcript construction is finite enumeration over the
`≤ L`-chunk tuples that `systemTreeSet_bounded_witness` licenses. -/

/-- The oracle of the compiled-tree reduction: the join of the two internal graphs. -/
def systemOracle {Ω : OmegaPart} (F : InternalInverseSystem Ω) : Set ℕ :=
  joinSet F.fibers.graph.1 F.bonding.graph.1

/-- **Oracle-relative fiber lookup**: the fiber enumerator's values are computable from
the join oracle — unique graph lookup, lifted along `left_le_joinSet`. -/
theorem fibers_eval_recursiveIn {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    Nat.RecursiveIn {charFn (systemOracle F)} (fun k => Part.some (F.fibers.eval k)) :=
  recursiveIn_of_turingReducible F.fibers.eval_recursiveIn_graph
    (left_le_joinSet _ _)

/-- **Oracle-relative bonding lookup**: same lookup, lifted along `right_le_joinSet`. -/
theorem bonding_eval_recursiveIn {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    Nat.RecursiveIn {charFn (systemOracle F)} (fun q => Part.some (F.bonding.eval q)) :=
  recursiveIn_of_turingReducible F.bonding.eval_recursiveIn_graph
    (right_le_joinSet _ _)

/-! ### The finite verifier

Everything below the two lookups is **finite**: no further search. The executable
definitions take **no proof fields** — only candidate index tuples, explicit bounds, and the
values `F.fibers.eval` / `F.bonding.eval`. Fiber nonemptiness, nodup, and `bonding_mem`
appear only in the soundness and completeness lemmas, which keeps the dependency claim
exact: *the computation uses the two graph lookups; the inverse-system laws justify it.*
All definitions are total, with explicit fallbacks on malformed input. -/

/-- The level-`k` fiber list, from the lookup alone. -/
noncomputable def fiberList {Ω : OmegaPart} (F : InternalInverseSystem Ω) (k : ℕ) :
    List ℕ :=
  decodeSeq (F.fibers.eval k)

/-- The chunk width at level `k` — the fiber-list length. -/
noncomputable def chunkWidth {Ω : OmegaPart} (F : InternalInverseSystem Ω) (k : ℕ) : ℕ :=
  (fiberList F k).length

/-- The element a level-`k` index selects; fallback `0` on an out-of-range index. -/
noncomputable def elemAt {Ω : OmegaPart} (F : InternalInverseSystem Ω) (k idx : ℕ) : ℕ :=
  (fiberList F k).getD idx 0

/-- The bit encoding of an index tuple, chunk by chunk from level `base` upward. Total on
any list of naturals. -/
noncomputable def encodeTuple {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ℕ → List ℕ → List ℕ
  | _, [] => []
  | base, idx :: rest =>
      bitListOfIndex (chunkWidth F base) idx ++ encodeTuple F (base + 1) rest

/-- The decidable bonding check against the previously chosen element. -/
noncomputable def bondOkB {Ω : OmegaPart} (F : InternalInverseSystem Ω) (base : ℕ)
    (prev : Option ℕ) (y : ℕ) : Bool :=
  match prev with
  | none => true
  | some x => decide (F.bonding.eval (Nat.pair (base - 1) y) = x)

theorem bondOkB_iff {Ω : OmegaPart} (F : InternalInverseSystem Ω) {base : ℕ}
    {prev : Option ℕ} {y : ℕ} : bondOkB F base prev y = true ↔ BondOk F base prev y := by
  cases prev with
  | none => simp [bondOkB, BondOk]
  | some x =>
    simp only [bondOkB, BondOk, decide_eq_true_eq]
    exact (F.bonding.mapsTo_iff_eval_eq).symm

/-- The finite verifier for one candidate tuple: every index is in range for its level, and
consecutive selections are bonding-coherent. Decidable and total — no proof fields, no
search. -/
noncomputable def tupleOk {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ℕ → Option ℕ → List ℕ → Bool
  | _, _, [] => true
  | base, prev, idx :: rest =>
      decide (idx < chunkWidth F base) &&
      bondOkB F base prev (elemAt F base idx) &&
      tupleOk F (base + 1) (some (elemAt F base idx)) rest

/-- All index tuples of length `j` whose entries are in range — a finite list, built from
the chunk widths alone. -/
noncomputable def candidateTuples {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (base : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | j + 1 =>
      (List.range (chunkWidth F base)).flatMap fun idx =>
        (candidateTuples F (base + 1) j).map fun t => idx :: t

/-- **The finite verifier for a tree node**: the code is a bit-sequence code, and some
candidate tuple of length at most the node's length passes `tupleOk` with the node's bits as
a prefix of its encoding. The bounded search is over `candidateTuples`, a finite list. -/
noncomputable def systemTreeVerifier {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (c : ℕ) : Bool :=
  (decodeSeq c).all (fun x => decide (x ≤ 1)) &&
  ((List.range ((decodeSeq c).length + 1)).any fun j =>
    (candidateTuples F 0 j).any fun t =>
      tupleOk F 0 none t && decide (decodeSeq c <+: encodeTuple F 0 t))

/-- Every entry of a candidate tuple is in range for its level, and the tuple has the
requested length — the totality/well-formedness lemma for the enumeration. -/
theorem mem_candidateTuples {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ {base j : ℕ} {t : List ℕ}, t ∈ candidateTuples F base j → t.length = j := by
  intro base j
  induction j generalizing base with
  | zero => intro t ht; simp only [candidateTuples, List.mem_singleton] at ht; simp [ht]
  | succ j ih =>
    intro t ht
    simp only [candidateTuples, List.mem_flatMap, List.mem_map, List.mem_range] at ht
    obtain ⟨idx, -, t', ht', rfl⟩ := ht
    simp [ih ht']

/-! #### Verifier ↔ `CoherentEncoding` correspondence -/

/-- **Soundness core**: a passing tuple encodes a coherent encoding. The inverse-system
laws enter here (through `pair_eval_mem` and the bonding correspondence), never in the
executable definitions. -/
theorem tupleOk_toCoherentEncoding {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ (base : ℕ) (prev : Option ℕ) (t : List ℕ), tupleOk F base prev t = true →
      CoherentEncoding F base prev t.length (encodeTuple F base t) := by
  intro base prev t
  induction t generalizing base prev with
  | nil => intro _; exact .nil _ _
  | cons idx rest ih =>
    intro h
    simp only [tupleOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, hbond⟩, hrest⟩ := h
    exact CoherentEncoding.cons (F.fibers.pair_eval_mem base) hlt
      (bondOkB_iff F |>.mp hbond) (ih _ _ hrest)

/-- **Completeness core**: every coherent encoding comes from a passing tuple. -/
theorem CoherentEncoding.exists_tuple {Ω : OmegaPart} {F : InternalInverseSystem Ω}
    {base : ℕ} {prev : Option ℕ} {j : ℕ} {full : List ℕ}
    (h : CoherentEncoding F base prev j full) :
    ∃ t, t.length = j ∧ encodeTuple F base t = full ∧ tupleOk F base prev t = true := by
  induction h with
  | nil k prev => exact ⟨[], rfl, rfl, rfl⟩
  | @cons k prev fc idx j rest hfc hidx hbond _ ih =>
    obtain ⟨t, hlen, henc, hok⟩ := ih
    have hfceq : F.fibers.eval k = fc := F.fibers.mapsTo_iff_eval_eq.mp hfc
    refine ⟨idx :: t, by simp [hlen], ?_, ?_⟩
    · change bitListOfIndex (chunkWidth F k) idx ++ encodeTuple F (k + 1) t = _
      rw [henc]
      congr 2
      change (decodeSeq (F.fibers.eval k)).length = _
      rw [hfceq]
    · have helem : elemAt F k idx = (decodeSeq fc).getD idx 0 := by
        change (decodeSeq (F.fibers.eval k)).getD idx 0 = _
        rw [hfceq]
      simp only [tupleOk, Bool.and_eq_true, decide_eq_true_eq, helem]
      refine ⟨⟨?_, (bondOkB_iff F).mpr hbond⟩, hok⟩
      change idx < (decodeSeq (F.fibers.eval k)).length
      rw [hfceq]; exact hidx

/-- A passing tuple is one of the enumerated candidates. -/
theorem tupleOk_mem_candidateTuples {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ (base : ℕ) (prev : Option ℕ) (t : List ℕ), tupleOk F base prev t = true →
      t ∈ candidateTuples F base t.length := by
  intro base prev t
  induction t generalizing base prev with
  | nil => intro _; simp [candidateTuples]
  | cons idx rest ih =>
    intro h
    simp only [tupleOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, -⟩, hrest⟩ := h
    simp only [List.length_cons, candidateTuples, List.mem_flatMap, List.mem_map,
      List.mem_range]
    exact ⟨idx, hlt, rest, ih _ _ hrest, rfl⟩

/-! #### Verifier soundness and completeness (separate, then combined) -/

/-- **Verifier soundness**: a passing code is a tree node. -/
theorem systemTreeVerifier_sound {Ω : OmegaPart} (F : InternalInverseSystem Ω) {c : ℕ}
    (h : systemTreeVerifier F c = true) : c ∈ systemTreeSet F := by
  simp only [systemTreeVerifier, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hbits, j, -, t, -, hok, hpre⟩ := h
  exact ⟨fun x hx => hbits x hx, t.length,
    encodeTuple F 0 t, tupleOk_toCoherentEncoding F 0 none t hok, hpre⟩

/-- **Verifier completeness**: every tree node passes. -/
theorem systemTreeVerifier_complete {Ω : OmegaPart} (F : InternalInverseSystem Ω) {c : ℕ}
    (h : c ∈ systemTreeSet F) : systemTreeVerifier F c = true := by
  obtain ⟨j, full, hj, henc, hpre⟩ := systemTreeSet_bounded_witness h
  obtain ⟨t, hlen, hteq, hok⟩ := henc.exists_tuple
  simp only [systemTreeVerifier, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  refine ⟨fun x hx => h.1 x hx, t.length, by omega, t, ?_, hok, by rw [hteq]; exact hpre⟩
  exact tupleOk_mem_candidateTuples F 0 none t hok

/-- **The bounded-search membership characterization**: the finite verifier decides tree
membership. -/
theorem systemTreeVerifier_correct {Ω : OmegaPart} (F : InternalInverseSystem Ω) (c : ℕ) :
    systemTreeVerifier F c = true ↔ c ∈ systemTreeSet F :=
  ⟨systemTreeVerifier_sound F, systemTreeVerifier_complete F⟩

/-! ### The table-driven implementation: finite oracle transcript, then pure verifier

`systemTreeVerifier` is the **semantic specification**, and stays so — the soundness and
completeness stack above is proved against it and is not touched here. What it cannot be is
`Nat.RecursiveIn`: it queries `F.fibers.eval` and `F.bonding.eval` at positions nested
inside list operations, and mathlib's oracle-relative library has no closure lemma for that
shape.

The reduction is therefore restructured into the normal form *finite oracle transcript,
then pure verifier*: the oracle is consulted only to build two finite tables, and
everything after that is a primitive-recursive function of those tables and the node code.
An agreement lemma attaches the implementation to the specification, so no correctness
proof moves. The same normal form is what later extraction and uniform-artifact work want —
the computability structure becomes an artifact rather than a proof detail.

Both tables are ragged lists of codes, each coded as one natural by `seqCode`:

* the **fiber table**'s row `base` is the fiber code `F.fibers.eval base`;
* the **bond table**'s row `base` lists, at index `idx`, the bonding image of the
  level-`base` element with index `idx`.

The bond table is keyed by `(base, idx)` — the level of the *argument*, not the first
coordinate of the bonding query. At level `base` the query is
`Nat.pair (base - 1) (elemAt F base idx)`, so a query whose first coordinate is `k` has its
argument in fiber `k + 1`; keying by `(k, y)` would be off by one, and would additionally
require searching a row for `y`, which positional keying avoids — so the pure verifier does
not depend on fiber `Nodup` even computationally. Row `0` of the bond table is unused.

Every accessor is total, falling back on `0` — the code of the empty list — for a missing
row or index, so the verifier is a total function of three naturals, primitive recursive
and (unlike the specification) genuinely computable. -/

/-- Row `base` of a table of codes; `0`, the code of `[]`, when the row is absent. -/
def tableRow (tbl base : ℕ) : ℕ :=
  (decodeSeq tbl).getD base 0

/-- The number of entries in row `base` of a table — for a fiber table, the chunk width. -/
def tableWidth (tbl base : ℕ) : ℕ :=
  (decodeSeq (tableRow tbl base)).length

/-- Entry `idx` of row `base` of a table; `0` when absent. For a fiber table this is the
selected element, for a bond table its bonding image. -/
def tableEntry (tbl base idx : ℕ) : ℕ :=
  (decodeSeq (tableRow tbl base)).getD idx 0

/-- One step of the table-driven tuple check. The state is
`(level, previously selected element, accepted so far)`; level `0` is the sentinel for
"no previous element", where the bonding check is skipped — matching `BondOk F 0 none`,
which is the only way the specification is ever entered. -/
def tupleOkStep (ft bt : ℕ) (st : ℕ × ℕ × Bool) (idx : ℕ) : ℕ × ℕ × Bool :=
  (st.1 + 1, tableEntry ft st.1 idx,
    st.2.2 && decide (idx < tableWidth ft st.1) &&
      (decide (st.1 = 0) || decide (tableEntry bt st.1 idx = st.2.1)))

/-- The table-driven tuple check: `tupleOk` read off the tables, as a left fold carrying
the level and the previously selected element. -/
def tupleOkT (ft bt : ℕ) (t : List ℕ) : Bool :=
  (t.foldl (tupleOkStep ft bt) (0, 0, true)).2.2

/-- One step of the table-driven chunk encoding; the state is `(level, bits so far)`. -/
def encodeTupleStep (ft : ℕ) (st : ℕ × List ℕ) (idx : ℕ) : ℕ × List ℕ :=
  (st.1 + 1, st.2 ++ bitListOfIndex (tableWidth ft st.1) idx)

/-- The table-driven chunk encoding of an index tuple, from level `0` upward. -/
def encodeTupleT (ft : ℕ) (t : List ℕ) : List ℕ :=
  (t.foldl (encodeTupleStep ft) (0, [])).2

/-- All in-range index tuples for levels `0, …, j - 1`, read off the fiber table. Tuples
are extended at the **end**, so the recursion carries no varying level parameter and is
primitive recursive in `(ft, j)` directly; the enumeration order differs from
`candidateTuples`, which is immaterial because only membership is ever used. -/
def tableTuples (ft : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | j + 1 =>
      (tableTuples ft j).flatMap fun t =>
        (List.range (tableWidth ft j)).map fun idx => t ++ [idx]

/-- **The table-driven verifier**: the specification's bounded search, with every oracle
query replaced by a table lookup. Prefixhood is phrased through `List.take` because that is
the form with primitive-recursive support. -/
def systemTreeVerifierFromTables (ft bt c : ℕ) : Bool :=
  (decodeSeq c).all (fun x => decide (x ≤ 1)) &&
  ((List.range ((decodeSeq c).length + 1)).any fun j =>
    (tableTuples ft j).any fun t =>
      tupleOkT ft bt t &&
        decide (decodeSeq c = (encodeTupleT ft t).take (decodeSeq c).length))

/-! #### The table-driven verifier is primitive recursive -/

theorem primrec_tableRow : Primrec₂ tableRow :=
  Primrec₂.comp (f := fun (l : List ℕ) (i : ℕ) => l.getD i 0) (Primrec.list_getD 0)
    (primrec_decodeSeq.comp .fst) .snd

theorem primrec_tableWidth : Primrec₂ tableWidth :=
  Primrec.list_length.comp (primrec_decodeSeq.comp primrec_tableRow)

theorem primrec_tableEntry :
    Primrec fun p : ℕ × ℕ × ℕ => tableEntry p.1 p.2.1 p.2.2 :=
  Primrec₂.comp (f := fun (l : List ℕ) (i : ℕ) => l.getD i 0) (Primrec.list_getD 0)
    (primrec_decodeSeq.comp
      (Primrec₂.comp primrec_tableRow .fst (Primrec.fst.comp .snd)))
    (Primrec.snd.comp .snd)

set_option maxHeartbeats 1000000 in
-- The fold state `ℕ × ℕ × Bool` and the parameter tuple `ℕ × ℕ × List ℕ` make
-- `Primcodable` instance elaboration for the composed product types expensive.
theorem primrec_tupleOkT :
    Primrec fun p : ℕ × ℕ × List ℕ => tupleOkT p.1 p.2.1 p.2.2 := by
  have hft : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ => q.1.1 :=
    Primrec.fst.comp .fst
  have hbt : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp .fst)
  have hlvl : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ => q.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp .snd)
  have hprev : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ => q.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp .snd))
  have hacc : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ => q.2.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .snd))
  have hidx : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ => q.2.2 :=
    Primrec.snd.comp .snd
  have hfib : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ =>
      tableEntry q.1.1 q.2.1.1 q.2.2 :=
    primrec_tableEntry.comp (hft.pair (hlvl.pair hidx))
  have hbond : Primrec fun q : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × Bool) × ℕ =>
      tableEntry q.1.2.1 q.2.1.1 q.2.2 :=
    primrec_tableEntry.comp (hbt.pair (hlvl.pair hidx))
  have hstep : Primrec₂ fun (p : ℕ × ℕ × List ℕ) (q : (ℕ × ℕ × Bool) × ℕ) =>
      tupleOkStep p.1 p.2.1 q.1 q.2 :=
    (Primrec.pair (Primrec.succ.comp hlvl)
      (Primrec.pair hfib
        (Primrec.and.comp
          (Primrec.and.comp hacc
            ((Primrec.nat_lt.comp hidx (Primrec₂.comp primrec_tableWidth hft hlvl)).decide))
          (Primrec.or.comp
            ((Primrec.eq.comp hlvl (Primrec.const 0)).decide)
            ((Primrec.eq.comp hbond hprev).decide))))).to₂
  have hfold : Primrec fun p : ℕ × ℕ × List ℕ =>
      p.2.2.foldl (fun s b => tupleOkStep p.1 p.2.1 s b) ((0, 0, true) : ℕ × ℕ × Bool) :=
    Primrec.list_foldl (f := fun p : ℕ × ℕ × List ℕ => p.2.2)
      (g := fun _ : ℕ × ℕ × List ℕ => ((0, 0, true) : ℕ × ℕ × Bool))
      (h := fun (p : ℕ × ℕ × List ℕ) (q : (ℕ × ℕ × Bool) × ℕ) => tupleOkStep p.1 p.2.1 q.1 q.2)
      (Primrec.snd.comp .snd) (Primrec.const _) hstep
  exact Primrec.snd.comp (Primrec.snd.comp hfold)

theorem primrec_encodeTupleT : Primrec₂ encodeTupleT := by
  have hft : Primrec fun q : (ℕ × List ℕ) × (ℕ × List ℕ) × ℕ => q.1.1 := Primrec.fst.comp .fst
  have hlvl : Primrec fun q : (ℕ × List ℕ) × (ℕ × List ℕ) × ℕ => q.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp .snd)
  have hbits : Primrec fun q : (ℕ × List ℕ) × (ℕ × List ℕ) × ℕ => q.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp .snd)
  have hidx : Primrec fun q : (ℕ × List ℕ) × (ℕ × List ℕ) × ℕ => q.2.2 := Primrec.snd.comp .snd
  have hstep : Primrec₂ fun (p : ℕ × List ℕ) (q : (ℕ × List ℕ) × ℕ) =>
      encodeTupleStep p.1 q.1 q.2 :=
    (Primrec.pair (Primrec.succ.comp hlvl)
      (Primrec₂.comp (f := fun l r : List ℕ => l ++ r)
        (g := fun q : (ℕ × List ℕ) × (ℕ × List ℕ) × ℕ => q.2.1.2)
        (h := fun q : (ℕ × List ℕ) × (ℕ × List ℕ) × ℕ =>
          bitListOfIndex (tableWidth q.1.1 q.2.1.1) q.2.2)
        Primrec.list_append hbits
        (Primrec₂.comp primrec_bitListOfIndex
          (Primrec₂.comp primrec_tableWidth hft hlvl) hidx))).to₂
  have hfold : Primrec fun p : ℕ × List ℕ =>
      p.2.foldl (fun s b => encodeTupleStep p.1 s b) ((0, []) : ℕ × List ℕ) :=
    Primrec.list_foldl (f := fun p : ℕ × List ℕ => p.2)
      (g := fun _ : ℕ × List ℕ => ((0, []) : ℕ × List ℕ))
      (h := fun (p : ℕ × List ℕ) (q : (ℕ × List ℕ) × ℕ) => encodeTupleStep p.1 q.1 q.2)
      Primrec.snd (Primrec.const _) hstep
  exact Primrec.snd.comp hfold

theorem tableTuples_eq_nat_rec (ft : ℕ) (j : ℕ) :
    tableTuples ft j =
      Nat.rec (motive := fun _ => List (List ℕ)) [[]]
        (fun j IH => IH.flatMap fun t => (List.range (tableWidth ft j)).map fun idx => t ++ [idx])
        j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [tableTuples, ih]

theorem primrec_tableTuples : Primrec₂ tableTuples := by
  have hinner : Primrec₂ fun (z : ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
      (List.range (tableWidth z.1 z.2.1)).map fun idx => t ++ [idx] :=
    Primrec.list_map
      (f := fun w : (ℕ × ℕ × List (List ℕ)) × List ℕ => List.range (tableWidth w.1.1 w.1.2.1))
      (g := fun (w : (ℕ × ℕ × List (List ℕ)) × List ℕ) (idx : ℕ) => w.2 ++ [idx])
      (Primrec.list_range.comp
        (Primrec₂.comp primrec_tableWidth (Primrec.fst.comp .fst)
          (Primrec.fst.comp (Primrec.snd.comp .fst))))
      (Primrec₂.comp (f := fun (l : List ℕ) (a : ℕ) => l ++ [a])
        (g := fun w : ((ℕ × ℕ × List (List ℕ)) × List ℕ) × ℕ => w.1.2)
        (h := fun w : ((ℕ × ℕ × List (List ℕ)) × List ℕ) × ℕ => w.2)
        Primrec.list_concat (Primrec.snd.comp .fst) .snd)
  have hg : Primrec₂ fun (ft : ℕ) (q : ℕ × List (List ℕ)) =>
      q.2.flatMap fun t => (List.range (tableWidth ft q.1)).map fun idx => t ++ [idx] :=
    Primrec.list_flatMap
      (f := fun z : ℕ × ℕ × List (List ℕ) => z.2.2)
      (g := fun (z : ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
        (List.range (tableWidth z.1 z.2.1)).map fun idx => t ++ [idx])
      (Primrec.snd.comp .snd) hinner
  exact (Primrec.nat_rec (Primrec.const [[]]) hg).of_eq fun ft j =>
    (tableTuples_eq_nat_rec ft j).symm

set_option maxHeartbeats 2000000 in
-- Three nested bounded searches over deeply nested product types; each `PrimrecRel`
-- composition re-elaborates the `Primcodable` instance for the enclosing product.
theorem systemTreeVerifierFromTables_primrec :
    Primrec fun p : ℕ × ℕ × ℕ => systemTreeVerifierFromTables p.1 p.2.1 p.2.2 := by
  classical
  -- The innermost parameter shape is `(tuple, ((fiberTable, bondTable, node), chunkCount))`.
  have hnode : Primrec fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => decodeSeq w.2.1.2.2 :=
    primrec_decodeSeq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .snd)))
  have hok : Primrec fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) =>
      tupleOkT w.2.1.1 w.2.1.2.1 w.1 :=
    primrec_tupleOkT.comp
      (g := fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => (w.2.1.1, w.2.1.2.1, w.1))
      ((Primrec.fst.comp (Primrec.fst.comp .snd)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp .snd))).pair .fst))
  have henc : Primrec fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => encodeTupleT w.2.1.1 w.1 :=
    Primrec₂.comp (f := encodeTupleT)
      (g := fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => w.2.1.1)
      (h := fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => w.1)
      primrec_encodeTupleT (Primrec.fst.comp (Primrec.fst.comp .snd)) .fst
  have hR₃ : PrimrecRel fun (t : List ℕ) (q : (ℕ × ℕ × ℕ) × ℕ) =>
      tupleOkT q.1.1 q.1.2.1 t = true ∧
        decodeSeq q.1.2.2 = (encodeTupleT q.1.1 t).take (decodeSeq q.1.2.2).length :=
    PrimrecPred.and (Primrec.eq.comp hok (Primrec.const true))
      (Primrec.eq.comp hnode
        (Primrec₂.comp (f := (List.take : ℕ → List ℕ → List ℕ))
          (g := fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => (decodeSeq w.2.1.2.2).length)
          (h := fun w : List ℕ × ((ℕ × ℕ × ℕ) × ℕ) => encodeTupleT w.2.1.1 w.1)
          Primrec.list_take (Primrec.list_length.comp hnode) henc))
  have hR₂ : PrimrecRel fun (j : ℕ) (p : ℕ × ℕ × ℕ) =>
      ∃ t ∈ tableTuples p.1 j, tupleOkT p.1 p.2.1 t = true ∧
        decodeSeq p.2.2 = (encodeTupleT p.1 t).take (decodeSeq p.2.2).length :=
    PrimrecRel.comp hR₃.exists_mem_list
      (Primrec₂.comp (f := tableTuples) (g := fun z : ℕ × ℕ × ℕ × ℕ => z.2.1)
        (h := fun z : ℕ × ℕ × ℕ × ℕ => z.1)
        primrec_tableTuples (Primrec.fst.comp .snd) .fst)
      (Primrec.pair (Primrec.snd) (Primrec.fst) :
        Primrec fun z : ℕ × ℕ × ℕ × ℕ => ((z.2, z.1) : (ℕ × ℕ × ℕ) × ℕ))
  have hlen : Primrec fun p : ℕ × ℕ × ℕ => (decodeSeq p.2.2).length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp (primrec_decodeSeq.comp (Primrec.snd.comp .snd)))
  have hsearch : PrimrecPred fun p : ℕ × ℕ × ℕ =>
      ∃ j ∈ List.range ((decodeSeq p.2.2).length + 1), ∃ t ∈ tableTuples p.1 j,
        tupleOkT p.1 p.2.1 t = true ∧
          decodeSeq p.2.2 = (encodeTupleT p.1 t).take (decodeSeq p.2.2).length :=
    PrimrecRel.comp hR₂.exists_mem_list (Primrec.list_range.comp hlen)
      (Primrec.id : Primrec fun p : ℕ × ℕ × ℕ => p)
  have hbit : PrimrecPred fun p : ℕ × ℕ × ℕ => ∀ x ∈ decodeSeq p.2.2, x ≤ 1 :=
    (PrimrecPred.forall_mem_list (p := fun x : ℕ => x ≤ 1)
      (Primrec.nat_le.comp Primrec.id (Primrec.const 1))).comp
      (primrec_decodeSeq.comp (Primrec.snd.comp .snd))
  obtain ⟨_inst, hmain⟩ := PrimrecPred.and hbit hsearch
  refine hmain.of_eq fun p => ?_
  rw [Bool.eq_iff_iff]
  simp only [systemTreeVerifierFromTables, decide_eq_true_eq, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]

/-! #### The ideal tables, and their bounded lookup equations

The transcripts the oracle has to produce. Both are truncations at a level bound `L`:
outside the bound the accessors return their fallbacks, and every agreement statement below
carries the bound it needs as `base + t.length ≤ L`. -/

/-- The **fiber transcript** up to level `L`: row `base` is the level-`base` fiber code. -/
noncomputable def fiberTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) (L : ℕ) : ℕ :=
  seqCode ((List.range L).map fun base => F.fibers.eval base)

/-- The **bond transcript** up to level `L`: row `base` lists, at index `idx`, the bonding
image of the level-`base` element with index `idx`. Row `0` is never read. -/
noncomputable def bondTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) (L : ℕ) : ℕ :=
  seqCode ((List.range L).map fun base =>
    seqCode ((List.range (chunkWidth F base)).map fun idx =>
      F.bonding.eval (Nat.pair (base - 1) (elemAt F base idx))))

theorem tableRow_fiberTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L base : ℕ}
    (h : base < L) : tableRow (fiberTable F L) base = F.fibers.eval base := by
  rw [tableRow, fiberTable, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range h, Option.map_some, Option.getD_some]

theorem tableWidth_fiberTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L base : ℕ}
    (h : base < L) : tableWidth (fiberTable F L) base = chunkWidth F base := by
  rw [tableWidth, tableRow_fiberTable F h, chunkWidth, fiberList]

theorem tableEntry_fiberTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L base : ℕ}
    (h : base < L) (idx : ℕ) : tableEntry (fiberTable F L) base idx = elemAt F base idx := by
  rw [tableEntry, tableRow_fiberTable F h, elemAt, fiberList]

theorem tableRow_bondTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L base : ℕ}
    (h : base < L) : tableRow (bondTable F L) base =
      seqCode ((List.range (chunkWidth F base)).map fun idx =>
        F.bonding.eval (Nat.pair (base - 1) (elemAt F base idx))) := by
  rw [tableRow, bondTable, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range h, Option.map_some, Option.getD_some]

theorem tableEntry_bondTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L base : ℕ}
    (h : base < L) {idx : ℕ} (hidx : idx < chunkWidth F base) :
    tableEntry (bondTable F L) base idx =
      F.bonding.eval (Nat.pair (base - 1) (elemAt F base idx)) := by
  rw [tableEntry, tableRow_bondTable F h, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hidx, Option.map_some, Option.getD_some]

/-! #### Agreement with the specification

Each lemma is an induction over the candidate tuple, with the level bound threaded through
as `base + t.length ≤ L`. The oracle-facing definitions are never unfolded: the tables enter
only through the four lookup equations above. -/

private theorem getD_concat_lt {t : List ℕ} {idx i : ℕ} (h : i < t.length) :
    (t ++ [idx]).getD i 0 = t.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_concat_self (t : List ℕ) (idx : ℕ) :
    (t ++ [idx]).getD t.length 0 = idx := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- The table-driven chunk encoding agrees with the specification's, level by level. -/
theorem encodeTupleStep_foldl {Ω : OmegaPart} (F : InternalInverseSystem Ω) (L : ℕ) :
    ∀ (t : List ℕ) (base : ℕ) (acc : List ℕ), base + t.length ≤ L →
      (t.foldl (encodeTupleStep (fiberTable F L)) (base, acc)).2 =
        acc ++ encodeTuple F base t := by
  intro t
  induction t with
  | nil => intro base acc _; simp [encodeTuple]
  | cons idx rest ih =>
    intro base acc h
    have hbase : base < L := by simp only [List.length_cons] at h; omega
    rw [List.foldl_cons, encodeTupleStep, tableWidth_fiberTable F hbase,
      ih (base + 1) _ (by simp only [List.length_cons] at h; omega), encodeTuple,
      List.append_assoc]

theorem encodeTupleT_eq {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L : ℕ} {t : List ℕ}
    (h : t.length ≤ L) : encodeTupleT (fiberTable F L) t = encodeTuple F 0 t := by
  have := encodeTupleStep_foldl F L t 0 [] (by omega)
  rw [encodeTupleT, this, List.nil_append]

/-- The table-driven tuple check agrees with the specification's above the root level. -/
theorem tupleOkStep_foldl_succ {Ω : OmegaPart} (F : InternalInverseSystem Ω) (L : ℕ) :
    ∀ (t : List ℕ) (base x : ℕ) (b : Bool), 1 ≤ base → base + t.length ≤ L →
      (t.foldl (tupleOkStep (fiberTable F L) (bondTable F L)) (base, x, b)).2.2 =
        (b && tupleOk F base (some x) t) := by
  intro t
  induction t with
  | nil => intro base x b _ _; simp [tupleOk]
  | cons idx rest ih =>
    intro base x b hb h
    have hbase : base < L := by simp only [List.length_cons] at h; omega
    have hrest : base + 1 + rest.length ≤ L := by simp only [List.length_cons] at h; omega
    have hzero : decide (base = 0) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [List.foldl_cons]
    simp only [tupleOkStep, hzero, Bool.false_or, tableWidth_fiberTable F hbase,
      tableEntry_fiberTable F hbase]
    by_cases hlt : idx < chunkWidth F base
    · rw [tableEntry_bondTable F hbase hlt, ih (base + 1) _ _ (by omega) hrest, tupleOk]
      have hbond : bondOkB F base (some x) (elemAt F base idx) =
          decide (F.bonding.eval (Nat.pair (base - 1) (elemAt F base idx)) = x) := rfl
      rw [hbond]
      simp [hlt, Bool.and_assoc]
    · rw [ih (base + 1) _ _ (by omega) hrest, tupleOk]
      simp [hlt]

theorem tupleOkT_eq {Ω : OmegaPart} (F : InternalInverseSystem Ω) {L : ℕ} {t : List ℕ}
    (h : t.length ≤ L) :
    tupleOkT (fiberTable F L) (bondTable F L) t = tupleOk F 0 none t := by
  match t with
  | [] => simp [tupleOkT, tupleOk]
  | idx :: rest =>
    have hzero : (0 : ℕ) < L := by simp only [List.length_cons] at h; omega
    have hrest : 1 + rest.length ≤ L := by simp only [List.length_cons] at h; omega
    rw [tupleOkT, List.foldl_cons, tupleOkStep, tableWidth_fiberTable F hzero,
      tableEntry_fiberTable F hzero]
    rw [tupleOkStep_foldl_succ F L rest 1 _ _ (le_refl 1) hrest, tupleOk]
    have hbond : bondOkB F 0 none (elemAt F 0 idx) = true := rfl
    rw [hbond]
    simp

/-! #### The two candidate enumerations have the same members -/

theorem mem_tableTuples_iff (ft : ℕ) : ∀ (j : ℕ) (t : List ℕ),
    t ∈ tableTuples ft j ↔ t.length = j ∧ ∀ i < j, t.getD i 0 < tableWidth ft i := by
  intro j
  induction j with
  | zero =>
    intro t
    simp only [tableTuples, List.mem_singleton, Nat.not_lt_zero, false_implies,
      implies_true, and_true, List.length_eq_zero_iff]
  | succ j ih =>
    intro t
    simp only [tableTuples, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t', ht', idx, hidx, rfl⟩
      obtain ⟨hlen, hall⟩ := (ih t').mp ht'
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      rcases Nat.lt_or_ge i t'.length with hi' | hi'
      · rw [getD_concat_lt hi']; exact hall i (hlen ▸ hi')
      · obtain rfl : i = t'.length := by omega
        rw [getD_concat_self]; exact hlen ▸ hidx
    · rintro ⟨hlen, hall⟩
      rcases List.eq_nil_or_concat t with rfl | ⟨t', idx, ht⟩
      · simp at hlen
      · rw [List.concat_eq_append] at ht
        subst ht
        have hlen' : t'.length = j := by simpa using hlen
        refine ⟨t', (ih t').mpr ⟨hlen', fun i hi => ?_⟩, idx, ?_, rfl⟩
        · rw [← getD_concat_lt (idx := idx) (by omega)]
          exact hall i (by omega)
        · have := hall t'.length (by omega)
          rwa [getD_concat_self, hlen'] at this

theorem mem_candidateTuples_iff {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ (j base : ℕ) (t : List ℕ), t ∈ candidateTuples F base j ↔
      t.length = j ∧ ∀ i < j, t.getD i 0 < chunkWidth F (base + i) := by
  intro j
  induction j with
  | zero =>
    intro base t
    simp only [candidateTuples, List.mem_singleton, Nat.not_lt_zero, false_implies,
      implies_true, and_true, List.length_eq_zero_iff]
  | succ j ih =>
    intro base t
    simp only [candidateTuples, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨idx, hidx, t', ht', rfl⟩
      obtain ⟨hlen, hall⟩ := (ih (base + 1) t').mp ht'
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      match i with
      | 0 => simpa using hidx
      | i + 1 =>
        have := hall i (by omega)
        simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using this
    · rintro ⟨hlen, hall⟩
      match t with
      | [] => simp at hlen
      | idx :: t' =>
        refine ⟨idx, by simpa using hall 0 (by omega), t',
          (ih (base + 1) t').mpr ⟨by simpa using hlen, fun i hi => ?_⟩, rfl⟩
        have := hall (i + 1) (by omega)
        simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using this

/-! #### The agreement lemma

The table-driven verifier computes the specification's verdict, provided the transcripts
reach the node's length. Every correctness theorem proved against the specification
therefore transports to the implementation unchanged. -/

theorem systemTreeVerifierFromTables_agrees {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (c : ℕ) {L : ℕ} (hL : (decodeSeq c).length ≤ L) :
    systemTreeVerifierFromTables (fiberTable F L) (bondTable F L) c =
      systemTreeVerifier F c := by
  rw [Bool.eq_iff_iff]
  simp only [systemTreeVerifierFromTables, systemTreeVerifier, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨j, hj, t, ht, hok, hpre⟩
    have hlen : t.length = j := ((mem_tableTuples_iff _ j t).mp ht).1
    have hle : t.length ≤ L := by omega
    rw [tupleOkT_eq F hle] at hok
    rw [encodeTupleT_eq F hle] at hpre
    exact ⟨j, hj, t, hlen ▸ tupleOk_mem_candidateTuples F 0 none t hok, hok,
      List.prefix_iff_eq_take.mpr hpre⟩
  · rintro ⟨j, hj, t, ht, hok, hpre⟩
    have hmem := (mem_candidateTuples_iff F j 0 t).mp ht
    have hle : t.length ≤ L := by omega
    refine ⟨j, hj, t, (mem_tableTuples_iff _ j t).mpr ⟨hmem.1, fun i hi => ?_⟩,
      by rw [tupleOkT_eq F hle]; exact hok,
      by rw [encodeTupleT_eq F hle]; exact List.prefix_iff_eq_take.mp hpre⟩
    rw [tableWidth_fiberTable F (by omega : i < L)]
    simpa using hmem.2 i hi

/-! #### The transcripts are finite oracle computations

Both tables are `valueTable`s, so both come from one oracle-relative primitive recursion.
The bond transcript needs a nested one: row `base` first reads the level-`base` fiber, then
queries the bonding map at each of its entries. -/

/-- The entry the bond transcript records at `(base, idx)`. -/
noncomputable def bondValue {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (base idx : ℕ) : ℕ :=
  F.bonding.eval (Nat.pair (base - 1) (elemAt F base idx))

/-- Row `base` of the bond transcript. -/
noncomputable def bondRow {Ω : OmegaPart} (F : InternalInverseSystem Ω) (base : ℕ) : ℕ :=
  valueTable (bondValue F base) (chunkWidth F base)

theorem fiberTable_eq_valueTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) (L : ℕ) :
    fiberTable F L = valueTable (fun base => F.fibers.eval base) L := rfl

theorem bondTable_eq_valueTable {Ω : OmegaPart} (F : InternalInverseSystem Ω) (L : ℕ) :
    bondTable F L = valueTable (bondRow F) L := rfl

theorem fiberTable_recursiveIn {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    Nat.RecursiveIn {charFn (systemOracle F)} fun L => Part.some (fiberTable F L) :=
  valueTable_recursiveIn (fibers_eval_recursiveIn F)

theorem bondValue_recursiveIn {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    Nat.RecursiveIn {charFn (systemOracle F)}
      fun m => Part.some (bondValue F m.unpair.1 m.unpair.2) := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hquery : Primrec fun z : ℕ =>
      Nat.pair (z.unpair.2.unpair.1 - 1) ((decodeSeq z.unpair.1).getD z.unpair.2.unpair.2 0) :=
    Primrec₂.comp (f := Nat.pair)
      (g := fun z : ℕ => z.unpair.2.unpair.1 - 1)
      (h := fun z : ℕ => (decodeSeq z.unpair.1).getD z.unpair.2.unpair.2 0)
      Primrec₂.natPair
      (Primrec.nat_sub.comp (hfst.comp hsnd) (Primrec.const 1))
      (Primrec₂.comp (f := fun (n i : ℕ) => (decodeSeq n).getD i 0)
        (g := fun z : ℕ => z.unpair.1) (h := fun z : ℕ => z.unpair.2.unpair.2)
        primrec_seqGet hfst (hsnd.comp hsnd))
  have hfib : Nat.RecursiveIn {charFn (systemOracle F)}
      fun m => Part.some (F.fibers.eval m.unpair.1) :=
    recursiveIn_comp_primrec (fibers_eval_recursiveIn F) hfst
  have hpair := recursiveIn_pair_total hfib (recursiveIn_of_primrec Primrec.id)
  have harg : Nat.RecursiveIn {charFn (systemOracle F)} fun m =>
      Part.some (Nat.pair (m.unpair.1 - 1) (elemAt F m.unpair.1 m.unpair.2)) :=
    (recursiveIn_comp_total (recursiveIn_of_primrec hquery) hpair).of_eq fun m => by
      simp only [Nat.unpair_pair, id_eq, elemAt, fiberList]
  exact recursiveIn_comp_total (bonding_eval_recursiveIn F) harg

theorem bondRow_recursiveIn {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    Nat.RecursiveIn {charFn (systemOracle F)} fun base => Part.some (bondRow F base) := by
  have hparam := valueTable_recursiveIn_param (bondValue_recursiveIn F)
  have hw : Nat.RecursiveIn {charFn (systemOracle F)}
      fun base => Part.some (Nat.pair base (chunkWidth F base)) :=
    (recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id)
      (recursiveIn_comp_total (recursiveIn_of_primrec primrec_seqLength)
        (fibers_eval_recursiveIn F))).of_eq fun base => by
      simp only [id_eq]; rfl
  exact (recursiveIn_comp_total hparam hw).of_eq fun base => by
    simp only [Nat.unpair_pair]; rfl

theorem bondTable_recursiveIn {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    Nat.RecursiveIn {charFn (systemOracle F)} fun L => Part.some (bondTable F L) :=
  valueTable_recursiveIn (bondRow_recursiveIn F)

/-! #### The compiled tree reduces to the system oracle -/

/-- **The `systemToTree` reduction**: tree membership is decided by a finite oracle
transcript followed by a primitive-recursive verifier, so the compiled tree is Turing
reducible to the join of the two internal graphs.

All unbounded search is confined to the two lookup channels — fiber lookup and bonding
lookup — invoked finitely many times, input-dependently, while materializing the
transcripts (roughly one fiber lookup per fiber-table row and one bonding lookup per
bond-table entry). Everything after transcript construction is pure primitive-recursive
computation. The inverse-system laws are used only to prove the verifier correct, never to
compute. -/
theorem systemTreeSet_le_systemOracle {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    systemTreeSet F ≤ᵀ systemOracle F := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hv : Primrec fun z : ℕ =>
      systemTreeVerifierFromTables z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 :=
    systemTreeVerifierFromTables_primrec.comp
      (g := fun z : ℕ => (z.unpair.1, z.unpair.2.unpair.1, z.unpair.2.unpair.2))
      (hfst.pair ((hfst.comp hsnd).pair (hsnd.comp hsnd)))
  have hlen : Nat.RecursiveIn {charFn (systemOracle F)}
      fun c => Part.some (decodeSeq c).length := recursiveIn_of_primrec primrec_seqLength
  have htriple := recursiveIn_pair_total
    (recursiveIn_comp_total (fiberTable_recursiveIn F) hlen)
    (recursiveIn_pair_total (recursiveIn_comp_total (bondTable_recursiveIn F) hlen)
      (recursiveIn_of_primrec Primrec.id))
  refine (recursiveIn_comp_total
    (recursiveIn_of_primrec (Primrec.cond hv (Primrec.const 1) (Primrec.const 0)))
    htriple).of_eq fun c => ?_
  simp only [Nat.unpair_pair, id_eq, charFn]
  rw [systemTreeVerifierFromTables_agrees F c (le_refl _)]
  by_cases hc : c ∈ systemTreeSet F
  · rw [if_pos hc, (systemTreeVerifier_correct F c).mpr hc]
    rfl
  · rw [if_neg hc, Bool.eq_false_iff.mpr fun h => hc ((systemTreeVerifier_correct F c).mp h)]
    rfl

end ReverseMathlib.Omega
