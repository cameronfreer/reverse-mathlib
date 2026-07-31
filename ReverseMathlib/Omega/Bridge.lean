/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.InverseSystem

/-!
# The WKLω ⇄ EFILCω bridge constructions (issue #22, slice 3, stage 2)

The four named constructions, each layered as: (1) raw set/function construction;
(2) relative-computability theorem; (3) packaging as `InternalSet`/`InternalFunction`;
(4) mathematical correctness. The layering prevents nonemptiness witnesses or `eval`
conveniences in correctness proofs from becoming hidden data dependencies. These
computability lemmas are simultaneously the future first ω-transfer rule set and the
source material for the represented uniform-reduction pilot.

This file begins the `treeToSystem` direction. Acceptance criteria (pinned in review):

* level enumerations are **structural** — indices `i < 2 ^ n` mapped to length-`n` bit
  lists, then their `seqCode`s filtered through the tree oracle — never a numerical scan
  of `seqCode` values, whose bijectivity carries no order property;
* the fiber graph is Turing-reducible to the tree; the bonding graph
  `(n, c) ↦ seqCode ((decodeSeq c).take n)` is recursive outright, independently of the
  tree;
* `HasNodeAtEveryLevel` is used only in correctness proofs — no selected node enters the
  constructed data.

Raw constructions are ambient-classical **sets** (graphs); their computability is a
separate layer-2 theorem about characteristic functions, never a claim that the Lean
definition is executable.
-/

namespace ReverseMathlib.Omega

/-- The length-`n` bit list of index `i` (bit `j` of `i`, little-endian): the structural
enumeration of all length-`n` bit vectors as `i` ranges below `2 ^ n`. -/
def bitListOfIndex (n i : ℕ) : List ℕ :=
  (List.range n).map fun j => if i.testBit j then 1 else 0

@[simp]
theorem bitListOfIndex_length (n i : ℕ) : (bitListOfIndex n i).length = n := by
  simp [bitListOfIndex]

theorem isBitSeqCode_seqCode_bitListOfIndex (n i : ℕ) :
    IsBitSeqCode (seqCode (bitListOfIndex n i)) := by
  intro x hx
  rw [decodeSeq_seqCode] at hx
  simp only [bitListOfIndex, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  split <;> omega

open Classical in
/-- Layer 1 (raw): the explicit level-`n` list of a tree — the `seqCode`s of all length-`n`
bit vectors, structurally enumerated, filtered by membership in `T`. Classical `decide` is
deliberate: this is an ambient set-level construction; its computability **relative to the
tree oracle** is the separate layer-2 theorem. -/
noncomputable def treeLevelList (T : Set ℕ) (n : ℕ) : List ℕ :=
  ((List.range (2 ^ n)).map fun i => seqCode (bitListOfIndex n i)).filter
    fun c => decide (c ∈ T)

/-- Layer 1 (raw): the fiber graph of the compiled inverse system — `Nat.pair n c` for `c`
the code of the level-`n` list. -/
noncomputable def treeFiberGraph (T : Set ℕ) : Set ℕ :=
  {p | ∃ n, p = Nat.pair n (seqCode (treeLevelList T n))}

/-- Layer 1 (raw): the bonding graph, recursive independently of the tree —
`Nat.pair (Nat.pair n c) c'` with `c' = seqCode ((decodeSeq c).take n)`: restriction is
truncation of the decoded node. -/
def treeBondingGraph : Set ℕ :=
  {p | ∃ n c, p = Nat.pair (Nat.pair n c) (seqCode ((decodeSeq c).take n))}

/-- Everything in a tree level decodes to a length-`n` member of the tree. -/
theorem mem_treeLevelList_iff {T : Set ℕ} {n c : ℕ} :
    c ∈ treeLevelList T n ↔
      c ∈ T ∧ ∃ i < 2 ^ n, c = seqCode (bitListOfIndex n i) := by
  classical
  simp only [treeLevelList, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hT⟩
    exact ⟨hT, i, hi, rfl⟩
  · rintro ⟨hT, i, hi, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hT⟩

/-! ### Layer 2: relative computability

The bonding graph is recursive outright — no tree oracle. The fiber graph is Turing
reducible to the tree: the level codes are computed by a primitive recursion whose step
queries the tree oracle at the structurally enumerated candidate. -/

/-- Membership in the bonding graph is an equation between primitive recursive values. -/
theorem mem_treeBondingGraph_iff {p : ℕ} :
    p ∈ treeBondingGraph ↔
      p.unpair.2 =
        seqCode ((decodeSeq p.unpair.1.unpair.2).take p.unpair.1.unpair.1) := by
  constructor
  · rintro ⟨n, c, rfl⟩
    simp [Nat.unpair_pair]
  · intro h
    refine ⟨p.unpair.1.unpair.1, p.unpair.1.unpair.2, ?_⟩
    rw [← h, Nat.pair_unpair, Nat.pair_unpair]

/-- The bonding graph is recursive, independently of any tree. -/
theorem recursiveSet_treeBondingGraph : RecursiveSet treeBondingGraph := by
  have hval : Primrec fun p : ℕ =>
      seqCode ((decodeSeq p.unpair.1.unpair.2).take p.unpair.1.unpair.1) := by
    have hfst : Primrec fun p : ℕ => p.unpair.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    have hsnd : Primrec fun p : ℕ => p.unpair.1.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    exact Primrec₂.comp (f := fun n k => seqCode ((decodeSeq n).take k))
      primrec_seqTake hsnd hfst
  have hchar : Primrec fun p : ℕ =>
      if p.unpair.2 =
          seqCode ((decodeSeq p.unpair.1.unpair.2).take p.unpair.1.unpair.1)
        then 1 else 0 :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) hval) (.const 1) (.const 0)
  have hp : Nat.Partrec fun p : ℕ => Part.some (if p.unpair.2 =
      seqCode ((decodeSeq p.unpair.1.unpair.2).take p.unpair.1.unpair.1)
        then 1 else 0) :=
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hchar)).of_eq fun _ => rfl
  refine hp.of_eq fun p => ?_
  simp only [charFn]
  by_cases h : p ∈ treeBondingGraph
  · rw [if_pos (mem_treeBondingGraph_iff.mp h), if_pos h]
  · rw [if_neg (fun hc => h (mem_treeBondingGraph_iff.mpr hc)), if_neg h]

/-- Append one entry to a coded sequence — primitive recursive. -/
private theorem primrec_snocCode : Primrec₂ fun ih x => seqCode (decodeSeq ih ++ [x]) :=
  primrec_seqCode.comp
    (Primrec₂.comp (f := fun (l m : List ℕ) => l ++ m) Primrec.list_append
      (primrec_decodeSeq.comp .fst)
      (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l) Primrec.list_cons
        .snd (.const [])))

/-- The structural candidate enumeration, arithmetically: bit `j` of `i` is
`i / 2 ^ j % 2`. -/
theorem bitListOfIndex_eq_div_mod (n i : ℕ) :
    bitListOfIndex n i = (List.range n).map fun j => i / 2 ^ j % 2 := by
  unfold bitListOfIndex
  refine List.map_congr_left fun j _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with h | h <;>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, h]

/-- The candidate code `seqCode (bitListOfIndex n i)` is primitive recursive in
`Nat.pair n i`. -/
private theorem primrec_candidate :
    Primrec fun p : ℕ => seqCode (bitListOfIndex p.unpair.1 p.unpair.2) := by
  have hinner : Primrec₂ fun (p : ℕ) (j : ℕ) => p.unpair.2 / 2 ^ j % 2 := by
    have hdiv : Primrec fun q : ℕ × ℕ => q.1.unpair.2 / 2 ^ q.2 :=
      Primrec₂.comp Primrec.nat_div
        (Primrec.snd.comp (Primrec.unpair.comp .fst))
        (Primrec₂.comp (f := fun (a b : ℕ) => a ^ b)
          (Primrec₂.unpaired'.mp Nat.Primrec.pow) (.const 2) .snd)
    exact Primrec₂.comp Primrec.nat_mod hdiv (.const 2)
  have hlist : Primrec fun p : ℕ =>
      (List.range p.unpair.1).map fun j => p.unpair.2 / 2 ^ j % 2 :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.fst.comp Primrec.unpair)) hinner
  refine (primrec_seqCode.comp hlist).of_eq fun p => ?_
  rw [bitListOfIndex_eq_div_mod]

open Classical in
/-- Layer 2 helper (raw): the code of the level list restricted to candidate indices below
`k` — the loop state of the oracle recursion. At `k = 2 ^ n` this is the full level code. -/
noncomputable def levelCodeUpTo (T : Set ℕ) (n k : ℕ) : ℕ :=
  seqCode (((List.range k).map fun i => seqCode (bitListOfIndex n i)).filter
    fun c => decide (c ∈ T))

open Classical in
/-- One step of the level recursion: test the `k`-th candidate against the tree. -/
theorem levelCodeUpTo_succ (T : Set ℕ) (n k : ℕ) :
    levelCodeUpTo T n (k + 1) =
      if seqCode (bitListOfIndex n k) ∈ T
        then seqCode (decodeSeq (levelCodeUpTo T n k) ++ [seqCode (bitListOfIndex n k)])
        else levelCodeUpTo T n k := by
  classical
  simp only [levelCodeUpTo, List.range_succ, List.map_append, List.filter_append,
    List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, decodeSeq_seqCode]
  by_cases h : seqCode (bitListOfIndex n k) ∈ T <;> simp [h]

/-- The full level code is the loop run to `2 ^ n`. -/
theorem seqCode_treeLevelList (T : Set ℕ) (n : ℕ) :
    seqCode (treeLevelList T n) = levelCodeUpTo T n (2 ^ n) :=
  rfl

/-- The level-code loop is computable relative to the tree oracle: a primitive recursion
whose step queries the tree at the structurally enumerated candidate and either appends it
or keeps the accumulator. The tree enters **only** as the oracle. -/
theorem levelCodeUpTo_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T}
      (fun p => Part.some (levelCodeUpTo T p.unpair.1 p.unpair.2)) := by
  classical
  have hcand : Nat.Partrec fun q => Part.some
      (seqCode (bitListOfIndex q.unpair.1 q.unpair.2.unpair.1)) := by
    have hcomp := primrec_candidate.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.unpair)
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    have : Primrec fun q : ℕ =>
        seqCode (bitListOfIndex q.unpair.1 q.unpair.2.unpair.1) :=
      hcomp.of_eq fun q => by rw [Nat.unpair_pair]
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hid : Nat.RecursiveIn {charFn T} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have horacle : Nat.RecursiveIn {charFn T} fun q =>
      charFn T (seqCode (bitListOfIndex q.unpair.1 q.unpair.2.unpair.1)) :=
    recursiveIn_comp_partrec (Nat.RecursiveIn.oracle (O := {charFn T}) _ rfl) hcand
  have hpair := hid.pair horacle
  have hpost : Nat.Partrec fun m => Part.some (if m.unpair.2 = 1
      then seqCode (decodeSeq m.unpair.1.unpair.2.unpair.2 ++
        [seqCode (bitListOfIndex m.unpair.1.unpair.1 m.unpair.1.unpair.2.unpair.1)])
      else m.unpair.1.unpair.2.unpair.2) := by
    have hq : Primrec fun m : ℕ => m.unpair.1 := Primrec.fst.comp Primrec.unpair
    have hi : Primrec fun m : ℕ => m.unpair.1.unpair.2.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hq)))
    have hcomp' := primrec_candidate.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp hq))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
        (Primrec.unpair.comp hq)))))
    have hcand' : Primrec fun m : ℕ =>
        seqCode (bitListOfIndex m.unpair.1.unpair.1 m.unpair.1.unpair.2.unpair.1) :=
      hcomp'.of_eq fun m => by rw [Nat.unpair_pair]
    have hval : Primrec fun m : ℕ => if m.unpair.2 = 1
        then seqCode (decodeSeq m.unpair.1.unpair.2.unpair.2 ++
          [seqCode (bitListOfIndex m.unpair.1.unpair.1 m.unpair.1.unpair.2.unpair.1)])
        else m.unpair.1.unpair.2.unpair.2 :=
      Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 1))
        (Primrec₂.comp (f := fun ih x => seqCode (decodeSeq ih ++ [x]))
          primrec_snocCode hi hcand')
        hi
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  have hstep := hpost.recursiveIn.comp hpair
  refine (Nat.RecursiveIn.prec
    (f := fun _ : ℕ => Part.some (seqCode ([] : List ℕ)))
    (((Nat.Partrec.of_primrec (Primrec.nat_iff.mp
      (Primrec.const (seqCode ([] : List ℕ))))).recursiveIn).of_eq fun _ => rfl)
    hstep).of_eq fun p => ?_
  rcases hp : Nat.unpair p with ⟨a, k⟩
  clear hp
  dsimp only
  induction k with
  | zero =>
    rw [Nat.rec_zero]
    simp [levelCodeUpTo]
  | succ y ih =>
    rw [← Nat.succ_eq_add_one]
    dsimp only
    rw [ih]
    simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
      Part.map_some, Nat.unpair_pair, levelCodeUpTo_succ]
    by_cases hmem : seqCode (bitListOfIndex a y) ∈ T
    · rw [if_pos hmem, if_pos rfl, if_pos hmem]
    · rw [if_neg hmem, if_neg (by omega), if_neg hmem]

/-- Membership in the fiber graph is an equation against the level code. -/
theorem mem_treeFiberGraph_iff {T : Set ℕ} {p : ℕ} :
    p ∈ treeFiberGraph T ↔ p.unpair.2 = seqCode (treeLevelList T p.unpair.1) := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [Nat.unpair_pair]
  · intro h
    exact ⟨p.unpair.1, by rw [← h, Nat.pair_unpair]⟩

/-- **Layer 2, `treeToSystem`**: the fiber graph is Turing-reducible to the tree. -/
theorem treeFiberGraph_le_tree (T : Set ℕ) : treeFiberGraph T ≤ᵀ T := by
  classical
  have hfull : Nat.RecursiveIn {charFn T}
      (fun p => Part.some (levelCodeUpTo T p.unpair.1 (2 ^ p.unpair.1))) := by
    have hpr : Nat.Partrec fun p => Part.some (Nat.pair p.unpair.1 (2 ^ p.unpair.1)) := by
      have : Primrec fun p : ℕ => Nat.pair p.unpair.1 (2 ^ p.unpair.1) :=
        Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
          (Primrec₂.comp (f := fun (a b : ℕ) => a ^ b)
            (Primrec₂.unpaired'.mp Nat.Primrec.pow) (.const 2)
            (Primrec.fst.comp Primrec.unpair))
      exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
    exact (recursiveIn_comp_partrec (levelCodeUpTo_recursiveIn T) hpr).of_eq fun p => by
      simp [Nat.unpair_pair]
  have hpaired := (((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq
    (fun (_ : ℕ) => rfl) : Nat.RecursiveIn {charFn T} fun q => Part.some q).pair hfull
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1.unpair.2 = m.unpair.2 then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1.unpair.2 = m.unpair.2 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpaired).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases h : p ∈ treeFiberGraph T
  · rw [if_pos (by rw [← seqCode_treeLevelList]; exact mem_treeFiberGraph_iff.mp h),
      if_pos h]
  · rw [if_neg (fun hc => h (mem_treeFiberGraph_iff.mpr
      (by rw [seqCode_treeLevelList]; exact hc))), if_neg h]

/-! ### Layer 3: internal packaging — no tree hypotheses

Totality and single-valuedness of the fiber and bonding graphs hold for an **arbitrary**
set `T`; Ω-membership comes from ideal closure applied to the layer-2 theorems. The
mathematical tree properties (`IsBinaryTreeCode`, `HasNodeAtEveryLevel`) enter only in
layer 4, where the `InternalInverseSystem` record is assembled — so "no selected node in
the constructed data" is literally true. -/

/-- The fiber enumerator of an internal set, as an internal graph-coded function. -/
def treeFiberFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω) (T : Ω.InternalSet) :
    InternalFunction Ω where
  graph := ⟨treeFiberGraph T.1, h.mem_of_reducible T.2 (treeFiberGraph_le_tree T.1)⟩
  total := fun n => ⟨seqCode (treeLevelList T.1 n), ⟨n, rfl⟩⟩
  singleValued := fun n y y' hy hy' => by
    obtain ⟨m, hm⟩ := hy
    obtain ⟨m', hm'⟩ := hy'
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    obtain ⟨h1, rfl⟩ := Nat.pair_eq_pair.mp hm'
    rw [h1]

/-- The bonding map (truncation of the decoded node), as an internal graph-coded function —
internal to **every** Turing ideal, since its graph is recursive. -/
def treeBondingFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω) : InternalFunction Ω where
  graph := ⟨treeBondingGraph, h.mem_of_recursive recursiveSet_treeBondingGraph⟩
  total := fun q => ⟨seqCode ((decodeSeq q.unpair.2).take q.unpair.1), by
    change _ ∈ treeBondingGraph
    rw [mem_treeBondingGraph_iff, Nat.unpair_pair]⟩
  singleValued := fun q y y' hy hy' => by
    have h1 := mem_treeBondingGraph_iff.mp hy
    have h2 := mem_treeBondingGraph_iff.mp hy'
    simp only [Nat.unpair_pair] at h1 h2
    rw [h1, h2]

/-! ### Layer 4 prerequisites: the enumeration is complete and duplicate-free

The structural enumeration hits every length-`n` bit vector exactly once below `2 ^ n`.
Completeness (`exists_bitListOfIndex`) is what lets `HasNodeAtEveryLevel` supply fiber
nonemptiness purely through a lemma — no chosen node is ever stored in data. -/

/-- The enumeration is injective below `2 ^ n`. -/
theorem bitListOfIndex_injOn {n : ℕ} :
    Set.InjOn (bitListOfIndex n) {i | i < 2 ^ n} := by
  intro i hi i' hi' hEq
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < n
  · have h1 := congrArg (fun l => l[j]?) hEq
    simp only [bitListOfIndex, List.getElem?_map, List.getElem?_range, hj] at h1
    rcases hti : i.testBit j <;> rcases hti' : i'.testBit j <;> simp_all
  · have hb : ∀ m : ℕ, m < 2 ^ n → m.testBit j = false := fun m hm => by
      have hmj : m < 2 ^ j :=
        lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (le_of_not_gt hj))
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hmj]
    rw [hb i hi, hb i' hi']

/-- **Completeness of the enumeration**: every bit list is `bitListOfIndex` of some index
below `2 ^ length`. -/
theorem exists_bitListOfIndex :
    ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 1) →
      ∃ i < 2 ^ l.length, bitListOfIndex l.length i = l := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, Nat.one_pos, rfl⟩
  | cons b t ih =>
    intro hbits
    obtain ⟨i, hi, hbi⟩ := ih fun x hx => hbits x (List.mem_cons_of_mem b hx)
    have hb : b ≤ 1 := hbits b List.mem_cons_self
    refine ⟨b + 2 * i, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      omega
    · have hcons : bitListOfIndex (t.length + 1) (b + 2 * i) =
          b :: bitListOfIndex t.length i := by
        unfold bitListOfIndex
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        · have hb2 : (b + 2 * i) % 2 = b := by omega
          rcases show b = 0 ∨ b = 1 by omega with rfl | rfl <;>
            simp [Nat.testBit_zero, hb2]
        · refine List.map_congr_left fun j _ => ?_
          have h2 : (b + 2 * i) / 2 = i := by omega
          simp [Function.comp, Nat.testBit_succ, h2]
      rw [show (b :: t).length = t.length + 1 from rfl, hcons, hbi]

/-- The level enumeration is duplicate-free: range nodup → injective enumeration →
injective coding → nodup map → nodup filter. -/
theorem treeLevelList_nodup (T : Set ℕ) (n : ℕ) : (treeLevelList T n).Nodup := by
  classical
  refine List.Nodup.filter _ (List.Nodup.map_on ?_ List.nodup_range)
  intro i hi i' hi' hEq
  exact bitListOfIndex_injOn (List.mem_range.mp hi) (List.mem_range.mp hi')
    (seqCode_injective hEq)

/-- The bonding normal form: truncating a level-`n + 1` enumeration entry lands exactly on
the level-`n` enumeration at the reduced index. -/
theorem bitListOfIndex_take (n i : ℕ) :
    (bitListOfIndex (n + 1) i).take n = bitListOfIndex n (i % 2 ^ n) := by
  rw [bitListOfIndex_eq_div_mod, bitListOfIndex_eq_div_mod, ← List.map_take,
    List.take_range, show min n (n + 1) = n by omega]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  have hsplit : 2 ^ n = 2 ^ j * 2 ^ (n - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : n - j ≠ 0))]

/-- **Layer 4: `treeToSystem`.** The tree hypotheses enter only here:
`HasNodeAtEveryLevel` supplies fiber nonemptiness purely through the completeness lemma
`exists_bitListOfIndex`, and prefix closure supplies `bonding_mem` through the bonding
normal form — no selected node is ever stored in the constructed data. -/
def treeToSystem {Ω : OmegaPart} (h : IsTuringIdeal Ω) (T : Ω.InternalSet)
    (htree : IsBinaryTreeCode T.1) (hlev : HasNodeAtEveryLevel T.1) :
    InternalInverseSystem Ω where
  fibers := treeFiberFunction h T
  bonding := treeBondingFunction h
  fiber_nodup := fun n c hc => by
    obtain ⟨m, hm⟩ := hc
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    rw [decodeSeq_seqCode]
    exact treeLevelList_nodup T.1 n
  fiber_nonempty := fun n c hc => by
    obtain ⟨m, hm⟩ := hc
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    rw [decodeSeq_seqCode]
    obtain ⟨c₀, hc₀T, hlen⟩ := hlev n
    obtain ⟨i, hi, hbl⟩ := exists_bitListOfIndex (decodeSeq c₀) (htree.1 c₀ hc₀T)
    rw [hlen] at hi hbl
    have hmem : c₀ ∈ treeLevelList T.1 n := by
      refine mem_treeLevelList_iff.mpr ⟨hc₀T, i, hi, ?_⟩
      conv_lhs => rw [← seqCode_decodeSeq c₀]
      rw [← hbl]
    intro hnil
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  bonding_mem := fun n c c' x y hc hc' hx hy => by
    obtain ⟨m, hm⟩ := hc
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    obtain ⟨m', hm'⟩ := hc'
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm'
    have h1 := mem_treeBondingGraph_iff.mp hy
    simp only [Nat.unpair_pair] at h1
    rw [decodeSeq_seqCode] at hx ⊢
    obtain ⟨hxT, i, hi, rfl⟩ := mem_treeLevelList_iff.mp hx
    refine mem_treeLevelList_iff.mpr
      ⟨?_, i % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n), ?_⟩
    · rw [h1]
      exact htree.2 _ hxT n
    · rw [h1, decodeSeq_seqCode, bitListOfIndex_take]

/-! ### `sectionToPath`: the decoded path

The raw predicate is the **specification**, mentioning only the section graph; the `rfind`
implementation will be proved extensionally equal to it, so answer-only access is
structural, never an after-the-fact dependency observation. The compiled tree first appears
in path correctness (stage 3). -/

/-- Layer 1 (raw, the specification): position `i` is on the decoded path iff the
level-`i + 1` section value carries bit `1` at position `i`. Mentions **only** the section
graph. -/
def sectionPathSet {Ω : OmegaPart} (s : InternalFunction Ω) : Set ℕ :=
  {i | ∃ c, s.MapsTo (i + 1) c ∧ (decodeSeq c).getD i 0 = 1}

/-- **Iterated section coherence**: a section value at any lower level is the truncation of
the value at any higher level. All intermediate-value selection happens inside this proof —
the reusable bridge between the level-`n` node and every level-`i + 1` inspection. -/
theorem section_value_take {Ω : OmegaPart} {h : IsTuringIdeal Ω} {T : Ω.InternalSet}
    {htree : IsBinaryTreeCode T.1} {hlev : HasNodeAtEveryLevel T.1}
    {s : InternalFunction Ω} (hs : (treeToSystem h T htree hlev).IsSection s) :
    ∀ {n k c c'}, k ≤ n → s.MapsTo n c → s.MapsTo k c' →
      c' = seqCode ((decodeSeq c).take k) := by
  -- Same-level normal form: every section value is a length-`level` node code.
  have hself : ∀ {m cm}, s.MapsTo m cm → cm = seqCode ((decodeSeq cm).take m) := by
    intro m cm hcm
    have hfib : (treeToSystem h T htree hlev).fibers.MapsTo m
        (seqCode (treeLevelList T.1 m)) := ⟨m, rfl⟩
    have hmem := hs.1 m _ cm hfib hcm
    rw [decodeSeq_seqCode] at hmem
    obtain ⟨-, i, -, rfl⟩ := mem_treeLevelList_iff.mp hmem
    rw [decodeSeq_seqCode, List.take_of_length_le (by simp)]
  intro n
  induction n with
  | zero =>
    intro k c c' hk hc hc'
    obtain rfl : k = 0 := by omega
    rw [s.singleValued 0 c' c hc' hc]
    exact hself hc
  | succ n ih =>
    intro k c c' hk hc hc'
    by_cases hkn : k = n + 1
    · subst hkn
      rw [s.singleValued _ c' c hc' hc]
      exact hself hc
    · have hk' : k ≤ n := by omega
      obtain ⟨cn, hcn⟩ := s.total n
      have hadj := hs.2 n c cn hc hcn
      have hbond := mem_treeBondingGraph_iff.mp hadj
      simp only [Nat.unpair_pair] at hbond
      rw [ih hk' hcn hc', hbond, decodeSeq_seqCode, List.take_take, min_eq_left hk']

open Classical in
/-- **Layer 2, `sectionToPath`**: the decoded path is Turing-reducible to the section
graph — this theorem mentions **only** `s.graph`; no tree appears. The implementation
searches (`rfind`) for a level-`i + 1` section value — totality guarantees termination,
single-valuedness makes the found value canonical — then inspects bit `i`; the proof shows
it extensionally equal to the raw specification. -/
theorem sectionPathSet_le_graph {Ω : OmegaPart} (s : InternalFunction Ω) :
    sectionPathSet s ≤ᵀ s.graph.1 := by
  classical
  have hpre : Nat.Partrec fun q => Part.some (Nat.pair (q.unpair.1 + 1) q.unpair.2) := by
    have : Primrec fun q : ℕ => Nat.pair (q.unpair.1 + 1) q.unpair.2 :=
      Primrec₂.natPair.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hqueried := recursiveIn_comp_partrec
    (Nat.RecursiveIn.oracle (O := {charFn s.graph.1}) _ rfl) hpre
  have hsub : Nat.Partrec fun m => Part.some (1 - m) := by
    have : Primrec fun m : ℕ => 1 - m := Primrec.nat_sub.comp (.const 1) .id
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hf := hsub.recursiveIn.comp hqueried
  have hrf := Nat.RecursiveIn.rfind hf
  have hid : Nat.RecursiveIn {charFn s.graph.1} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpaired := hid.pair hrf
  have hpost : Nat.Partrec fun m => Part.some
      (if (decodeSeq m.unpair.2).getD m.unpair.1 0 = 1 then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if (decodeSeq m.unpair.2).getD m.unpair.1 0 = 1 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
          (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair))
        (.const 1)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpaired).of_eq fun i => ?_
  obtain ⟨y, hy⟩ := s.total (i + 1)
  have hex : ∃ y, Nat.pair (i + 1) y ∈ s.graph.1 := ⟨y, hy⟩
  have hy₀ : Nat.pair (i + 1) (Nat.find hex) ∈ s.graph.1 := Nat.find_spec hex
  have hiff : i ∈ sectionPathSet s ↔ (decodeSeq (Nat.find hex)).getD i 0 = 1 := by
    constructor
    · rintro ⟨c, hc, hbit⟩
      rwa [s.singleValued _ c (Nat.find hex) hc hy₀] at hbit
    · exact fun hbit => ⟨Nat.find hex, hy₀, hbit⟩
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  have hrfeq : (Nat.rfind fun n => Part.some
      (decide ((1 - if Nat.pair (i + 1) n ∈ s.graph.1 then 1 else 0) = 0))) =
      Part.some (Nat.find hex) := by
    rw [Part.eq_some_iff, Nat.mem_rfind]
    constructor
    · simp [hy₀]
    · intro m hm
      have hnm : Nat.pair (i + 1) m ∉ s.graph.1 := fun hmem => Nat.find_min hex hm hmem
      simp [hnm]
  rw [hrfeq]
  simp only [Part.map_some, Part.bind_some, Nat.unpair_pair]
  by_cases hbit : (decodeSeq (Nat.find hex)).getD i 0 = 1
  · rw [if_pos hbit, if_pos (hiff.mpr hbit)]
  · rw [if_neg hbit, if_neg fun hc => hbit (hiff.mp hc)]

/-- Layer 3: the decoded path as an internal set — ideal closure on the layer-2
reducibility. No tree hypotheses; the tree first appears in path correctness. -/
def sectionPathInternal {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (s : InternalFunction Ω) : Ω.InternalSet :=
  ⟨sectionPathSet s, h.mem_of_reducible s.graph.2 (sectionPathSet_le_graph s)⟩

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

end ReverseMathlib.Omega
