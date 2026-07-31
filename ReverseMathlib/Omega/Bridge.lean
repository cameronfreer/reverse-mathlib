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

end ReverseMathlib.Omega
