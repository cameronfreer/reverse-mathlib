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

end ReverseMathlib.Omega
