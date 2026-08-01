/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.GetD
import ReverseMathlib.Omega.SystemToTree

/-!
# `pathToSection`: decoding a path through the compiled tree (issue #22, slice 3)

The decoder paired with `systemToTree`. A path through the compiled tree selects, in every
level-`k` chunk, the bit block of a fiber index; reading the blocks back yields a section
of the original system. The layers of the discipline:

* **Raw decoder** (`pathSectionValue`, `pathSectionGraph`): a *total* function of the fiber
  enumerator and the path — chunk boundaries from the fiber widths (`chunkStart`), the
  index from the chunk's raw bits (`natOfBits`), the element by `getD` with fallback `0`
  on malformed input.
* **Computability** (`pathSectionGraph_le_join`): the decoder's **fine dependency is
  enforced in its type** — it takes only the fiber enumerator and the path, so the
  reduction states exactly `pathSectionGraph fibers P ≤ᵀ joinSet fibers.graph.1 P.1`. The
  bonding graph cannot enter: it is not in scope.
* **Packaging** (`pathSectionFunction`): the decoded section as an internal graph-coded
  function, internal by Turing-ideal closure under the join.
* **Correctness** (`pathSectionFunction_isSection`): only here does the full
  `InternalInverseSystem` appear — the bonding laws justify the decoded values but never
  feed the computation, structurally rather than as a closure observation.

The computability argument is again in the normal form *finite oracle transcript, then
pure verifier*: the only unbounded-search channel is fiber lookup (the unique-graph-value
search), invoked finitely many times, input-dependently — once per level up to the queried
one; the path enters through single-answer bit queries while materializing each level's
finite chunk transcript, and everything after transcript construction is pure
primitive-recursive computation.
-/

namespace ReverseMathlib.Omega

/-! ### Layer 1: the raw decoder -/

open Classical in
/-- The bit of a set at a position — `charFn` as a total natural-valued function. -/
noncomputable def pathBit (A : Set ℕ) (i : ℕ) : ℕ :=
  if i ∈ A then 1 else 0

theorem charFn_eq_pathBit (A : Set ℕ) : charFn A = fun n => Part.some (pathBit A n) := rfl

/-- The chunk width the decoder uses at level `k` — the fiber-list length, read from the
fiber enumerator alone. On `F.fibers` this is `chunkWidth F` (`fiberWidth_chunkWidth`). -/
noncomputable def fiberWidth {Ω : OmegaPart} (fibers : InternalFunction Ω) (k : ℕ) : ℕ :=
  (decodeSeq (fibers.eval k)).length

theorem fiberWidth_chunkWidth {Ω : OmegaPart} (F : InternalInverseSystem Ω) (k : ℕ) :
    fiberWidth F.fibers k = chunkWidth F k := rfl

/-- The bit position where the level-`k` chunk starts: the sum of the widths below. -/
noncomputable def chunkStart {Ω : OmegaPart} (fibers : InternalFunction Ω) : ℕ → ℕ
  | 0 => 0
  | k + 1 => chunkStart fibers k + fiberWidth fibers k

theorem chunkStart_eq_nat_rec {Ω : OmegaPart} (fibers : InternalFunction Ω) (L : ℕ) :
    chunkStart fibers L = Nat.rec (motive := fun _ => ℕ) 0
      (fun y ih => ih + fiberWidth fibers y) L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [chunkStart, ih]

/-- The level-`k` chunk of the path, as a raw bit list. -/
noncomputable def pathChunkBits {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) (k : ℕ) : List ℕ :=
  (List.range (fiberWidth fibers k)).map fun j => pathBit P.1 (chunkStart fibers k + j)

/-- The fiber index the level-`k` chunk selects, read back from the raw bits. -/
noncomputable def pathIndex {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) (k : ℕ) : ℕ :=
  natOfBits (pathChunkBits fibers P k)

/-- **The raw decoder**: the element the path selects at level `k` — entry `pathIndex` of
the level-`k` fiber list, with fallback `0` out of range. Total on every input. -/
noncomputable def pathSectionValue {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) (k : ℕ) : ℕ :=
  (decodeSeq (fibers.eval k)).getD (pathIndex fibers P k) 0

/-- The graph of the decoder, as a set of `Nat.pair` codes. -/
def pathSectionGraph {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) : Set ℕ :=
  {m | pathSectionValue fibers P m.unpair.1 = m.unpair.2}

theorem isGraphOf_pathSectionGraph {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) :
    IsGraphOf (pathSectionGraph fibers P) (pathSectionValue fibers P) := fun x y => by
  simp [pathSectionGraph, Nat.unpair_pair, Set.mem_setOf_eq]

/-! ### Layer 2: the decoder is computable from the fiber graph joined with the path

The **fine dependency is the type**: only the fiber enumerator and the path are in scope,
so the oracle of this reduction is `joinSet fibers.graph.1 P.1`, and the bonding graph
cannot appear. The only unbounded-search channel is fiber lookup
(`InternalFunction.eval_recursiveIn_graph`); the path is consulted through single-answer
bit queries while materializing each level's finite chunk transcript (a `valueTable`), and
everything after transcript construction is pure primitive-recursive computation
(`natOfBits`, `getD`). -/

/-- The decoded value is computable from the join of the fiber graph and the path. -/
theorem pathSectionValue_recursiveIn {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) :
    Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun k => Part.some (pathSectionValue fibers P k) := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  -- the two oracle channels
  have heval : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun k => Part.some (fibers.eval k) :=
    recursiveIn_of_turingReducible fibers.eval_recursiveIn_graph (left_le_joinSet _ _)
  have hbit : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun i => Part.some (pathBit P.1 i) := by
    have h : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)} (charFn P.1) :=
      right_le_joinSet fibers.graph.1 P.1
    rwa [charFn_eq_pathBit] at h
  -- widths and chunk starts
  have hwidth : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun k => Part.some (fiberWidth fibers k) :=
    (recursiveIn_comp_total (f := fun n => (decodeSeq n).length)
      (g := fun k => fibers.eval k)
      (recursiveIn_of_primrec primrec_seqLength) heval).of_eq fun k => rfl
  have hstart : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun k => Part.some (chunkStart fibers k) := by
    have hstep : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
        fun m => Part.some (m.unpair.2 + fiberWidth fibers m.unpair.1) := by
      have h1 := recursiveIn_comp_primrec hwidth hfst
      have h2 := recursiveIn_pair_total h1 (recursiveIn_of_primrec hsnd)
      exact (recursiveIn_comp_total
        (recursiveIn_of_primrec (Primrec.nat_add.comp hsnd hfst)) h2).of_eq fun m => by
          simp only [Nat.unpair_pair]
    exact (recursiveIn_nat_rec (base := 0)
      (step := fun y ih => ih + fiberWidth fibers y) hstep).of_eq fun L => by
        rw [chunkStart_eq_nat_rec]
  -- the chunk transcript
  have harg : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun m => Part.some (chunkStart fibers m.unpair.1 + m.unpair.2) := by
    have h1 := recursiveIn_comp_primrec hstart hfst
    have h2 := recursiveIn_pair_total h1 (recursiveIn_of_primrec hsnd)
    exact (recursiveIn_comp_total
      (recursiveIn_of_primrec (Primrec.nat_add.comp hfst hsnd)) h2).of_eq fun m => by
        simp only [Nat.unpair_pair]
  have htable : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun k => Part.some (valueTable
        (fun j => pathBit P.1 (chunkStart fibers k + j)) (fiberWidth fibers k)) := by
    have hparam := valueTable_recursiveIn_param
      (f := fun a j => pathBit P.1 (chunkStart fibers a + j))
      (recursiveIn_comp_total hbit harg)
    have hkw := recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id) hwidth
    exact (recursiveIn_comp_total hparam hkw).of_eq fun k => by
      simp only [Nat.unpair_pair, id_eq]
  -- index and value: pure post-processing of the transcript
  have hindex : Nat.RecursiveIn {charFn (joinSet fibers.graph.1 P.1)}
      fun k => Part.some (pathIndex fibers P k) := by
    have hpost : Primrec fun n : ℕ => natOfBits (decodeSeq n) :=
      primrec_natOfBits.comp primrec_decodeSeq
    exact (recursiveIn_comp_total (recursiveIn_of_primrec hpost) htable).of_eq fun k => by
      rw [decodeSeq_valueTable]
      simp only [pathIndex, pathChunkBits]
  have hget : Primrec fun z : ℕ => (decodeSeq z.unpair.1).getD z.unpair.2 0 :=
    Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet hfst hsnd
  exact (recursiveIn_comp_total (recursiveIn_of_primrec hget)
    (recursiveIn_pair_total heval hindex)).of_eq fun k => by
      simp only [Nat.unpair_pair, pathSectionValue]

/-- **The decoder's reduction**: the graph of the decoded section is Turing reducible to
the join of the fiber graph and the path — the exact fine dependency, stated on exactly the
data the decoder's type admits. -/
theorem pathSectionGraph_le_join {Ω : OmegaPart} (fibers : InternalFunction Ω)
    (P : Ω.InternalSet) : pathSectionGraph fibers P ≤ᵀ joinSet fibers.graph.1 P.1 := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hval := recursiveIn_comp_primrec (pathSectionValue_recursiveIn fibers P) hfst
  have hpair := recursiveIn_pair_total hval (recursiveIn_of_primrec Primrec.id)
  have hpost : Primrec fun z : ℕ => if z.unpair.1 = z.unpair.2.unpair.2 then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hfst (hsnd.comp hsnd)) (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun m => ?_
  simp only [Nat.unpair_pair, id_eq, charFn]
  by_cases hm : pathSectionValue fibers P m.unpair.1 = m.unpair.2
  · rw [if_pos hm, if_pos (show m ∈ pathSectionGraph fibers P from hm)]
  · rw [if_neg hm, if_neg (show m ∉ pathSectionGraph fibers P from hm)]

/-! ### Layer 3: internal packaging -/

/-- The decoded section as an internal graph-coded function — internal by Turing-ideal
closure under the join of the fiber graph and the path. Still only the fine dependency in
the type. -/
def pathSectionFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (fibers : InternalFunction Ω) (P : Ω.InternalSet) : InternalFunction Ω where
  graph := ⟨pathSectionGraph fibers P,
    h.mem_of_reducible (h.join fibers.graph.2 P.2) (pathSectionGraph_le_join fibers P)⟩
  total x := ⟨pathSectionValue fibers P x,
    (isGraphOf_pathSectionGraph fibers P x _).mpr rfl⟩
  singleValued x y y' hy hy' :=
    ((isGraphOf_pathSectionGraph fibers P x y).mp hy).symm.trans
      ((isGraphOf_pathSectionGraph fibers P x y').mp hy')

/-- The relational surface of the packaged decoder. -/
theorem pathSectionFunction_mapsTo_iff {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (fibers : InternalFunction Ω) (P : Ω.InternalSet) {n v : ℕ} :
    (pathSectionFunction h fibers P).MapsTo n v ↔ pathSectionValue fibers P n = v :=
  isGraphOf_pathSectionGraph fibers P n v

/-! ### Layer 4: correctness — a path through the compiled tree decodes to a section

Only here does the full `InternalInverseSystem` enter. The plan: a genuine path agrees, at
every bit length, with some tree node; a node long enough to cover the first `n + 1`
chunks is a prefix of the encoding of one coherent passing tuple, so the decoder's raw
chunk bits *are* that tuple's `bitListOfIndex` blocks, and `natOfBits` reads the tuple's
indices back exactly (`natOfBits_bitListOfIndex` plus in-range-ness from `tupleOk`). Fiber
membership and bonding coherence of the decoded values are then positional facts about the
passing tuple. -/

private theorem fiberWidth_pos {Ω : OmegaPart} (F : InternalInverseSystem Ω) (k : ℕ) :
    0 < fiberWidth F.fibers k :=
  List.length_pos_iff.mpr (F.fiber_nonempty k _ (F.fibers.pair_eval_mem k))

private theorem chunkStart_le_chunkStart {Ω : OmegaPart} (fibers : InternalFunction Ω)
    {m k : ℕ} (h : m ≤ k) : chunkStart fibers m ≤ chunkStart fibers k := by
  induction k with
  | zero => obtain rfl := Nat.le_zero.mp h; exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega)).trans (Nat.le_add_right _ _)

private theorem chunkStart_lt_chunkStart {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    {m k : ℕ} (h : m < k) : chunkStart F.fibers m < chunkStart F.fibers k :=
  calc chunkStart F.fibers m < chunkStart F.fibers (m + 1) := by
        have := fiberWidth_pos F m
        change chunkStart F.fibers m < chunkStart F.fibers m + fiberWidth F.fibers m
        omega
    _ ≤ chunkStart F.fibers k := chunkStart_le_chunkStart _ h

/-- The encoding of a tuple occupies exactly the chunk positions its levels own. -/
private theorem encodeTuple_length {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ (t : List ℕ) (base : ℕ),
      (encodeTuple F base t).length + chunkStart F.fibers base =
        chunkStart F.fibers (base + t.length) := by
  intro t
  induction t with
  | nil => intro base; simp [encodeTuple]
  | cons idx rest ih =>
    intro base
    have hrec := ih (base + 1)
    have hsucc : chunkStart F.fibers (base + 1) =
        chunkStart F.fibers base + fiberWidth F.fibers base := rfl
    have hw : chunkWidth F base = fiberWidth F.fibers base := rfl
    have harith : base + (idx :: rest).length = base + 1 + rest.length := by
      simp only [List.length_cons]; omega
    rw [harith]
    simp only [encodeTuple, List.length_append, bitListOfIndex_length]
    omega

private theorem encodeTuple_zero_length {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (t : List ℕ) : (encodeTuple F 0 t).length = chunkStart F.fibers t.length := by
  have h := encodeTuple_length F t 0
  have h0 : chunkStart F.fibers 0 = 0 := rfl
  rw [Nat.zero_add] at h
  omega

/-- Splitting the encoding at a chunk boundary. -/
private theorem encodeTuple_split {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ (m : ℕ) (t : List ℕ) (base : ℕ),
      encodeTuple F base t =
        encodeTuple F base (t.take m) ++ encodeTuple F (base + m) (t.drop m) := by
  intro m
  induction m with
  | zero => intro t base; simp [encodeTuple]
  | succ m ih =>
    intro t base
    match t with
    | [] => simp [encodeTuple]
    | idx :: rest =>
      have e : base + (m + 1) = base + 1 + m := by omega
      simp only [List.take_succ_cons, List.drop_succ_cons, encodeTuple, e,
        ih rest (base + 1), List.append_assoc]

/-- Bit `j` of the level-`k` chunk of an encoded tuple is bit `j` of the level's
`bitListOfIndex` block. -/
private theorem encodeTuple_getD_chunk {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    (t : List ℕ) {k : ℕ} (hk : k < t.length) {j : ℕ} (hj : j < chunkWidth F k) :
    (encodeTuple F 0 t).getD (chunkStart F.fibers k + j) 0 =
      (bitListOfIndex (chunkWidth F k) (t.getD k 0)).getD j 0 := by
  have hlen : (encodeTuple F 0 (t.take k)).length = chunkStart F.fibers k := by
    rw [encodeTuple_zero_length F (t.take k), List.length_take,
      Nat.min_eq_left (le_of_lt hk)]
  have hgetD : t.getD k 0 = t[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have hdrop : t.drop k = t.getD k 0 :: t.drop (k + 1) := by
    rw [hgetD]
    exact List.drop_eq_getElem_cons hk
  rw [encodeTuple_split F k t 0, hdrop]
  simp only [Nat.zero_add, encodeTuple, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  have hidx : chunkStart F.fibers k + j - (encodeTuple F 0 (t.take k)).length = j := by
    omega
  rw [hidx, List.getElem?_append_left (by simpa using hj)]

/-- Positional in-range facts of a passing tuple. -/
private theorem tupleOk_getD_lt {Ω : OmegaPart} (F : InternalInverseSystem Ω) {t : List ℕ}
    (h : tupleOk F 0 none t = true) : ∀ i < t.length, t.getD i 0 < chunkWidth F i := by
  have h2 := (mem_candidateTuples_iff F t.length 0 t).mp
    (tupleOk_mem_candidateTuples F 0 none t h)
  intro i hi
  simpa using h2.2 i hi

/-- Positional bonding facts of a passing tuple: consecutive selected elements are
bonding-coherent. -/
private theorem tupleOk_bond_getD {Ω : OmegaPart} (F : InternalInverseSystem Ω) :
    ∀ (t : List ℕ) (base : ℕ) (prev : Option ℕ), tupleOk F base prev t = true →
      ∀ k, k + 1 < t.length →
        F.bonding.eval (Nat.pair (base + k)
            (elemAt F (base + k + 1) (t.getD (k + 1) 0))) =
          elemAt F (base + k) (t.getD k 0) := by
  intro t
  induction t with
  | nil => intro base prev _ k hk; simp at hk
  | cons idx rest ih =>
    intro base prev h k hk
    simp only [tupleOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨-, -⟩, hrest⟩ := h
    match k with
    | 0 =>
      cases rest with
      | nil => simp at hk
      | cons y rest' =>
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        simp only [tupleOk, Bool.and_eq_true, decide_eq_true_eq] at hrest
        obtain ⟨⟨-, hbond'⟩, -⟩ := hrest
        simp only [bondOkB, decide_eq_true_eq, Nat.add_sub_cancel] at hbond'
        simpa [Nat.add_zero] using hbond'
    | k + 1 =>
      have e : base + (k + 1) = base + 1 + k := by omega
      simp only [List.getD_cons_succ]
      rw [e]
      exact ih (base + 1) _ hrest k (by simp only [List.length_cons] at hk; omega)

/-- **The decoding lemma**: a path through the compiled tree pins the decoder's chunk
indices, up to any level bound, to those of one coherent passing tuple. -/
private theorem exists_tuple_decoding {Ω : OmegaPart} (F : InternalInverseSystem Ω)
    {P : Ω.InternalSet} (hP : IsBinaryPathThrough P.1 (systemTreeSet F)) (n : ℕ) :
    ∃ t : List ℕ, tupleOk F 0 none t = true ∧ n < t.length ∧
      ∀ k ≤ n, pathIndex F.fibers P k = t.getD k 0 := by
  obtain ⟨c, hcT, hclen, hagree⟩ := hP (chunkStart F.fibers (n + 1))
  obtain ⟨hbits, j, full, henc, hpre⟩ := hcT
  obtain ⟨t, htlen, htfull, hok⟩ := henc.exists_tuple
  have hfull_len : full.length = chunkStart F.fibers t.length := by
    rw [← htfull, encodeTuple_zero_length]
  have hn : n < t.length := by
    by_contra hle
    have h1 : chunkStart F.fibers (n + 1) ≤ full.length := hclen ▸ hpre.length_le
    have h2 : chunkStart F.fibers t.length ≤ chunkStart F.fibers n :=
      chunkStart_le_chunkStart _ (by omega)
    have h3 : chunkStart F.fibers n < chunkStart F.fibers (n + 1) :=
      chunkStart_lt_chunkStart F (Nat.lt_succ_self n)
    omega
  refine ⟨t, hok, hn, fun k hk => ?_⟩
  have hchunk : pathChunkBits F.fibers P k =
      bitListOfIndex (chunkWidth F k) (t.getD k 0) := by
    have hlen_eq : (pathChunkBits F.fibers P k).length = chunkWidth F k := by
      simp [pathChunkBits, fiberWidth_chunkWidth]
    apply List.ext_getElem (by simp [hlen_eq])
    intro i h1 h2
    have hi : i < chunkWidth F k := by simpa [hlen_eq] using h1
    have hpos_lt : chunkStart F.fibers k + i < chunkStart F.fibers (n + 1) := by
      have hle1 : chunkStart F.fibers (k + 1) ≤ chunkStart F.fibers (n + 1) :=
        chunkStart_le_chunkStart _ (by omega)
      have hsucc : chunkStart F.fibers (k + 1) =
          chunkStart F.fibers k + fiberWidth F.fibers k := rfl
      have hw : fiberWidth F.fibers k = chunkWidth F k := rfl
      omega
    have hentry : (pathChunkBits F.fibers P k)[i] =
        pathBit P.1 (chunkStart F.fibers k + i) := by
      simp [pathChunkBits]
    have hcbit : (decodeSeq c).getD (chunkStart F.fibers k + i) 0 =
        pathBit P.1 (chunkStart F.fibers k + i) := by
      have hlt : chunkStart F.fibers k + i < (decodeSeq c).length := by omega
      have hmem_le : (decodeSeq c).getD (chunkStart F.fibers k + i) 0 ≤ 1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact hbits _ (List.getElem_mem hlt)
      have hiff := hagree (chunkStart F.fibers k + i) (by omega)
      by_cases hmemP : chunkStart F.fibers k + i ∈ P.1
      · rw [hiff.mpr hmemP]
        simp only [pathBit]
        rw [if_pos hmemP]
      · have hne : (decodeSeq c).getD (chunkStart F.fibers k + i) 0 ≠ 1 :=
          fun hc => hmemP (hiff.mp hc)
        simp only [pathBit]
        rw [if_neg hmemP]
        omega
    have hcfull : (decodeSeq c).getD (chunkStart F.fibers k + i) 0 =
        full.getD (chunkStart F.fibers k + i) 0 := by
      obtain ⟨r, hr⟩ := hpre
      rw [← hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega : chunkStart F.fibers k + i <
          (decodeSeq c).length)]
    have hfull_bit : full.getD (chunkStart F.fibers k + i) 0 =
        (bitListOfIndex (chunkWidth F k) (t.getD k 0)).getD i 0 := by
      rw [← htfull]
      exact encodeTuple_getD_chunk F t (by omega) hi
    have hbit_i : (bitListOfIndex (chunkWidth F k) (t.getD k 0))[i] =
        (bitListOfIndex (chunkWidth F k) (t.getD k 0)).getD i 0 :=
      (List.getD_eq_getElem _ _ h2).symm
    rw [hentry, ← hcbit, hcfull, hfull_bit, ← hbit_i]
  have hklt : t.getD k 0 < chunkWidth F k := tupleOk_getD_lt F hok k (by omega)
  change natOfBits (pathChunkBits F.fibers P k) = t.getD k 0
  rw [hchunk, natOfBits_bitListOfIndex]
  exact Nat.mod_eq_of_lt (lt_trans hklt (Nat.lt_two_pow_self))

/-- **Correctness**: a path through the compiled tree decodes to a section of the system.
Only this theorem takes the full `InternalInverseSystem` — the bonding laws justify the
decoded values but never feed the computation. -/
theorem pathSectionFunction_isSection {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (F : InternalInverseSystem Ω) {P : Ω.InternalSet}
    (hP : IsBinaryPathThrough P.1 (systemTreeSet F)) :
    F.IsSection (pathSectionFunction h F.fibers P) := by
  constructor
  · intro n c v hfc hv
    rw [pathSectionFunction_mapsTo_iff] at hv
    subst hv
    obtain ⟨t, hok, hn, hidx⟩ := exists_tuple_decoding F hP n
    have heval : F.fibers.eval n = c := F.fibers.mapsTo_iff_eval_eq.mp hfc
    have hlt : t.getD n 0 < (decodeSeq (F.fibers.eval n)).length :=
      tupleOk_getD_lt F hok n (by omega)
    rw [← heval]
    change (decodeSeq (F.fibers.eval n)).getD (pathIndex F.fibers P n) 0 ∈
      decodeSeq (F.fibers.eval n)
    rw [hidx n le_rfl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
    exact List.getElem_mem hlt
  · intro n v v' hv hv'
    rw [pathSectionFunction_mapsTo_iff] at hv hv'
    obtain ⟨t, hok, hn, hidx⟩ := exists_tuple_decoding F hP (n + 1)
    have hval : pathSectionValue F.fibers P (n + 1) =
        elemAt F (n + 1) (t.getD (n + 1) 0) := by
      change (decodeSeq (F.fibers.eval (n + 1))).getD (pathIndex F.fibers P (n + 1)) 0 = _
      rw [hidx (n + 1) le_rfl]; rfl
    have hval' : pathSectionValue F.fibers P n = elemAt F n (t.getD n 0) := by
      change (decodeSeq (F.fibers.eval n)).getD (pathIndex F.fibers P n) 0 = _
      rw [hidx n (by omega)]; rfl
    have hbond := tupleOk_bond_getD F t 0 none hok n (by omega)
    simp only [Nat.zero_add] at hbond
    apply F.bonding.mapsTo_iff_eval_eq.mpr
    rw [← hv, ← hv', hval, hval']
    exact hbond

end ReverseMathlib.Omega
