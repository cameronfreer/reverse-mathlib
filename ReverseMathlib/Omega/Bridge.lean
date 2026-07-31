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

-- The bridge file is over the default length limit; the split into bit coding,
-- `treeToSystem`, `systemToTree`, and the equivalence is the next commit.
set_option linter.style.longFile 1700

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

/-- **Layer 2, `sectionToPath`**: the decoded path is Turing-reducible to the section
graph — this theorem mentions **only** `s.graph`; no tree appears. The implementation is
unique graph lookup at level `i + 1` followed by a primitive recursive bit inspection;
totality guarantees termination and single-valuedness makes the found value canonical. -/
theorem sectionPathSet_le_graph {Ω : OmegaPart} (s : InternalFunction Ω) :
    sectionPathSet s ≤ᵀ s.graph.1 := by
  classical
  have hsucc : Nat.Partrec fun i => Part.some (i + 1) := by
    have : Primrec fun i : ℕ => i + 1 := Primrec.succ
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have heval := recursiveIn_comp_partrec s.eval_recursiveIn_graph hsucc
  have hid : Nat.RecursiveIn {charFn s.graph.1} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpost : Nat.Partrec fun m => Part.some
      (if (decodeSeq m.unpair.2).getD m.unpair.1 0 = 1 then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if (decodeSeq m.unpair.2).getD m.unpair.1 0 = 1 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
          (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair))
        (.const 1)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp (hid.pair heval)).of_eq fun i => ?_
  have hiff : i ∈ sectionPathSet s ↔ (decodeSeq (s.eval (i + 1))).getD i 0 = 1 := by
    constructor
    · rintro ⟨c, hc, hbit⟩
      have : s.eval (i + 1) = c := s.mapsTo_iff_eval_eq.mp hc
      rwa [this]
    · exact fun hbit => ⟨s.eval (i + 1), s.pair_eval_mem _, hbit⟩
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases hbit : (decodeSeq (s.eval (i + 1))).getD i 0 = 1
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

/-! ### First direction: `EFILCω → WKLω`

The integration of the completed `treeToSystem` / `sectionToPath` route. Deliberately an
**ordinary unregistered theorem**: it is registered only when both directions and the exact
semantic equivalence certificate land atomically (stage 5). Selection of the level-`n`
section value happens purely inside this proof; the constructed path is
`sectionPathInternal`, whose definition and reducibility mention only the section graph. -/

/-- **`EFILCω → WKLω`** over a Turing ideal: compile the tree to an internal inverse system
(`treeToSystem`), take a section, and decode it to an internal path (`sectionPathInternal`).
Path correctness runs the four steps: select a level-`n` section value proof-locally; fiber
membership yields a genuine length-`n` tree node; `section_value_take` relates it to every
level-`i + 1` value; the relational path statement converts the bit. -/
theorem weakKonigAt_of_efilcAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hefilc : EFILCAt Ω) : WeakKonigAt Ω := by
  intro T htree hlev
  obtain ⟨s, hs⟩ := hefilc (treeToSystem h T htree hlev)
  refine ⟨sectionPathInternal h s, fun n => ?_⟩
  -- Step 1: select the level-`n` section value — proof-local.
  obtain ⟨cn, hcn⟩ := s.total n
  -- Step 2: fiber membership makes it a genuine length-`n` tree node.
  have hfib : (treeToSystem h T htree hlev).fibers.MapsTo n
      (seqCode (treeLevelList T.1 n)) := ⟨n, rfl⟩
  have hmem := hs.1 n _ cn hfib hcn
  rw [decodeSeq_seqCode] at hmem
  obtain ⟨hcnT, idx, hidx, hcneq⟩ := mem_treeLevelList_iff.mp hmem
  have hlen : (decodeSeq cn).length = n := by
    rw [hcneq, decodeSeq_seqCode, bitListOfIndex_length]
  refine ⟨cn, hcnT, hlen, fun i hi => ?_⟩
  -- Step 3: iterated coherence relates the level-`n` node to the level-`i + 1` value.
  obtain ⟨ci, hci⟩ := s.total (i + 1)
  have htake : ci = seqCode ((decodeSeq cn).take (i + 1)) :=
    section_value_take (h := h) (T := T) (htree := htree) (hlev := hlev) hs
      (by omega) hcn hci
  -- Step 4: the relational path statement converts the bit at position `i`.
  have hbit : (decodeSeq ci).getD i 0 = (decodeSeq cn).getD i 0 := by
    rw [htake, decodeSeq_seqCode, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  constructor
  · intro hone
    exact ⟨ci, hci, by rw [hbit]; exact hone⟩
  · rintro ⟨c', hc', hone⟩
    rw [s.singleValued _ c' ci hc' hci, hbit] at hone
    exact hone

/-! ### `systemToTree` layer 2, stage 1: oracle-relative lookups

The join of the fiber and bonding graphs is the single oracle. Level and bonding values are
found by terminating searches — the **only** unbounded steps in the whole reduction;
everything downstream is finite enumeration over the `≤ L`-chunk tuples that
`systemTreeSet_bounded_witness` licenses. -/

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

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_bitListOfIndex : Primrec₂ bitListOfIndex := by
  have h : Primrec fun p : ℕ × ℕ => (List.range p.1).map fun j => p.2 / 2 ^ j % 2 :=
    Primrec.list_map (Primrec.list_range.comp .fst)
      (Primrec.nat_mod.comp
        (Primrec.nat_div.comp (Primrec.snd.comp .fst)
          (Primrec₂.comp primrec_natPow (Primrec.const 2) .snd))
        (Primrec.const 2)).to₂
  exact h.of_eq fun p => (bitListOfIndex_eq_div_mod p.1 p.2).symm

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

The two unbounded searches are exactly the two graph lookups inside the transcript; the
inverse-system laws are used only to prove the verifier correct, never to compute. -/
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
