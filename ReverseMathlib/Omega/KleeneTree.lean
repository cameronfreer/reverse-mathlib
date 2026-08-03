/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.PartrecCode
import ReverseMathlib.Omega.Tree

/-!
# The Kleene tree: REC fails weak Kőnig's lemma (tranche 4, first certified separation)

The explicit diagonal construction of a **recursive infinite binary tree with no recursive
infinite path**, and the resulting countermodel: the recursive-set Turing ideal
`recursivePart` (REC) does not satisfy `WeakKonigAt`.

The construction uses **bounded universal computation** rather than importing any packaged
nonimplication: at length `n`, the diagonal computations `φ_e(e)` for `e < n` are inspected
through mathlib's step-bounded evaluator `Nat.Partrec.Code.evaln` with step bound `n`, and
bit `e` of a tree node is required to disagree with any computation observed within that
bound. Time-bound monotonicity (`evaln_mono`) gives prefix closure; flipping each observed
bit gives a node at every level; and for a recursive path the eventual discovery of its own
diagonal index yields the contradiction.

Literature: Kleene's diagonal counterexample to Kőnig's lemma for recursive trees
(S. C. Kleene, *Recursive functions and intuitionistic mathematics*, Proc. ICM Cambridge
1950; cf. the REC discussion in [Sim09] §VIII.2) — citation claimed, not verified against a
pinned corpus snapshot.

Everything here is ambient Lean over standard ℕ; the separation acquires its ω-scope
meaning only through the registered semantic context of its certificate
(`ReverseMathlib/Ports/Omega/RecWkl.lean`), never through these statements themselves.
-/

namespace ReverseMathlib.Omega

open Nat.Partrec (Code)

/-! ### The diagonal observation and the tree -/

/-- The bounded diagonal observation: the result (if any) of running the `e`-th partial
recursive function on its own index `e`, within `n` steps of mathlib's step-bounded
universal evaluator. -/
def diagObserved (n e : ℕ) : Option ℕ :=
  Nat.Partrec.Code.evaln n (Denumerable.ofNat Code e) e

/-- Time-bound monotonicity: an observation survives any larger bound. This is what makes
prefix closure of the Kleene tree work. -/
theorem diagObserved_mono {m n e v : ℕ} (h : m ≤ n) (hv : diagObserved m e = some v) :
    diagObserved n e = some v :=
  Nat.Partrec.Code.evaln_mono h hv

/-- The Kleene constraint on a decoded node: bit `e` disagrees with every diagonal
computation observed within `l.length` steps. -/
def KleeneConstraint (l : List ℕ) : Prop :=
  ∀ e < l.length, ∀ v, diagObserved l.length e = some v → l.getD e 0 ≠ v % 2

/-- **The Kleene tree**: bit-sequence codes whose decoded nodes satisfy the diagonal
disagreement constraint. -/
def kleeneTree : Set ℕ :=
  {c | IsBitSeqCode c ∧ KleeneConstraint (decodeSeq c)}

/-! ### Tree structure: binary, prefix closed, a node at every level -/

/-- The Kleene tree is a binary tree code: bit-valued and prefix closed. Prefix closure is
exactly time-bound monotonicity — a constraint observed at the shorter length was already
observed at the longer one. -/
theorem isBinaryTreeCode_kleeneTree : IsBinaryTreeCode kleeneTree := by
  refine ⟨fun c hc => hc.1, fun c hc k => ?_⟩
  obtain ⟨hbits, hcon⟩ := hc
  set l := decodeSeq c with hl
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [decodeSeq_seqCode] at hx
    exact hbits x (List.mem_of_mem_take hx)
  · intro e he v hv
    rw [decodeSeq_seqCode] at he hv ⊢
    have hlen : (l.take k).length ≤ l.length := by
      simp [List.length_take]
    have hobs : diagObserved l.length e = some v := diagObserved_mono hlen hv
    have helt : e < l.length := lt_of_lt_of_le he hlen
    have hne := hcon e helt v hobs
    have hgd : (l.take k).getD e 0 = l.getD e 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he, Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem helt, Option.getD_some]
      exact List.getElem_take
    rw [hgd]
    exact hne

/-- The canonical level-`n` node: flip every diagonal bit observed within `n` steps. -/
def kleeneWitness (n : ℕ) : List ℕ :=
  (List.range n).map fun e =>
    match diagObserved n e with
    | some v => 1 - v % 2
    | none => 0

@[simp]
theorem length_kleeneWitness (n : ℕ) : (kleeneWitness n).length = n := by
  simp [kleeneWitness]

theorem getD_kleeneWitness {n e : ℕ} (he : e < n) :
    (kleeneWitness n).getD e 0 =
      match diagObserved n e with
      | some v => 1 - v % 2
      | none => 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using he),
    Option.getD_some]
  simp [kleeneWitness]

/-- The Kleene tree has a node at every level: the flipped-bit witness satisfies the
constraint outright. -/
theorem hasNodeAtEveryLevel_kleeneTree : HasNodeAtEveryLevel kleeneTree := by
  intro n
  refine ⟨seqCode (kleeneWitness n), ⟨?_, ?_⟩, by rw [decodeSeq_seqCode]; simp⟩
  · intro x hx
    rw [decodeSeq_seqCode] at hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    cases diagObserved n e <;> simp
  · intro e he v hv
    rw [decodeSeq_seqCode] at he hv ⊢
    rw [length_kleeneWitness] at he hv
    rw [getD_kleeneWitness he, hv]
    change 1 - v % 2 ≠ v % 2
    have : v % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

/-! ### Membership is recursive

The tree constraint is a bounded search: bit-valuedness is a scan of the decoded node, and
the diagonal constraint inspects only the finitely many step-bounded computations
`evaln l.length · ·` — mathlib's `primrec_evaln` makes the whole check primitive
recursive. -/

/-- The Boolean membership check for the Kleene tree — the decision function whose
primitive recursiveness makes the tree internal to REC. -/
def kleeneCheck (c : ℕ) : Bool :=
  ((decodeSeq c).all fun x => decide (x ≤ 1)) &&
    ((List.range (decodeSeq c).length).all fun e =>
      match diagObserved (decodeSeq c).length e with
      | some v => !decide ((decodeSeq c).getD e 0 = v % 2)
      | none => true)

/-- The check decides membership. -/
theorem kleeneCheck_eq_true_iff {c : ℕ} : kleeneCheck c = true ↔ c ∈ kleeneTree := by
  simp only [kleeneCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine and_congr Iff.rfl (forall_congr' fun e => forall_congr' fun _ => ?_)
  cases h : diagObserved (decodeSeq c).length e with
  | none => simp
  | some v =>
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · intro hne v' hv'
      exact (Option.some_injective _ hv') ▸ hne
    · exact fun hall => hall v rfl

/-- Folding form of `List.all`, for the primitive-recursion combinators. -/
private theorem list_all_eq_foldr {α : Type} (p : α → Bool) (l : List α) :
    l.all p = l.foldr (fun a acc => p a && acc) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The membership check is primitive recursive: bounded universal computation via
mathlib's `Nat.Partrec.Code.primrec_evaln`, composed with the sequence-coding
primitives. -/
theorem primrec_kleeneCheck : Primrec kleeneCheck := by
  have hlen : Primrec fun c : ℕ => (decodeSeq c).length := primrec_seqLength
  have hand : Primrec₂ fun (a b : Bool) => a && b := Primrec.dom_bool₂ (· && ·)
  -- first conjunct: the bit scan
  have hle1 : Primrec fun q : ℕ × (ℕ × Bool) => decide (q.2.1 ≤ 1) :=
    PrimrecPred.decide
      (Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
  have hbitStep : Primrec₂ fun (_ : ℕ) (p : ℕ × Bool) => decide (p.1 ≤ 1) && p.2 :=
    (hand.comp hle1 (Primrec.snd.comp Primrec.snd)).to₂
  have hbits : Primrec fun c : ℕ => (decodeSeq c).all fun x => decide (x ≤ 1) :=
    (Primrec.list_foldr primrec_decodeSeq (Primrec.const true) hbitStep).of_eq
      fun c => by rw [list_all_eq_foldr]
  -- the diagonal observation, as a function of the pair (c, e)
  have hdiag : Primrec₂ diagObserved :=
    (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.pair ((Primrec.ofNat _).comp Primrec.snd)).pair Primrec.snd))).to₂
  -- the per-index constraint check
  have heqd : Primrec fun q : (ℕ × ℕ) × ℕ =>
      decide ((decodeSeq q.1.1).getD q.1.2 0 = q.2 % 2) :=
    PrimrecPred.decide (Primrec.eq.comp
      (primrec_seqGet.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)))
  have hinner : Primrec fun q : (ℕ × ℕ) × ℕ =>
      !decide ((decodeSeq q.1.1).getD q.1.2 0 = q.2 % 2) :=
    (Primrec.dom_bool Bool.not).comp heqd
  have hcheck : Primrec fun p : ℕ × ℕ =>
      match diagObserved (decodeSeq p.1).length p.2 with
      | some v => !decide ((decodeSeq p.1).getD p.2 0 = v % 2)
      | none => true := by
    have hobs : Primrec fun p : ℕ × ℕ => diagObserved (decodeSeq p.1).length p.2 :=
      hdiag.comp (hlen.comp Primrec.fst) Primrec.snd
    exact (Primrec.option_casesOn hobs (Primrec.const true) hinner.to₂).of_eq fun p => by
      cases diagObserved (decodeSeq p.1).length p.2 <;> rfl
  -- second conjunct: the range scan
  have hdiagStep : Primrec₂ fun (c : ℕ) (p : ℕ × Bool) =>
      (match diagObserved (decodeSeq c).length p.1 with
        | some v => !decide ((decodeSeq c).getD p.1 0 = v % 2)
        | none => true) && p.2 :=
    (hand.comp
      (hcheck.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hrange : Primrec fun c : ℕ => List.range (decodeSeq c).length :=
    Primrec.list_range.comp hlen
  have hcon : Primrec fun c : ℕ => (List.range (decodeSeq c).length).all fun e =>
      match diagObserved (decodeSeq c).length e with
      | some v => !decide ((decodeSeq c).getD e 0 = v % 2)
      | none => true :=
    (Primrec.list_foldr hrange (Primrec.const true) hdiagStep).of_eq
      fun c => by rw [list_all_eq_foldr]
  exact (hand.comp hbits hcon).of_eq fun c => rfl

/-- **The Kleene tree is recursive** — hence internal to every Turing ideal, in particular
to REC. -/
theorem recursiveSet_kleeneTree : RecursiveSet kleeneTree := by
  have hchar : Primrec fun c : ℕ => (bif kleeneCheck c then 1 else 0 : ℕ) :=
    Primrec.cond primrec_kleeneCheck (Primrec.const 1) (Primrec.const 0)
  have hp : Nat.Partrec fun c : ℕ => Part.some (bif kleeneCheck c then 1 else 0 : ℕ) :=
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hchar)).of_eq fun _ => rfl
  refine hp.of_eq fun c => ?_
  simp only [charFn]
  by_cases h : c ∈ kleeneTree
  · rw [kleeneCheck_eq_true_iff.mpr h, if_pos h]
    rfl
  · rw [Bool.eq_false_iff.mpr fun hc => h (kleeneCheck_eq_true_iff.mp hc), if_neg h]
    rfl

/-! ### No recursive path

A recursive path would be a recursive set `P`; its characteristic function has a code, and
the self-application of that code halts with the path's own bit at the code's index. Beyond
that stage the tree constraint forces the path's node to disagree with itself. -/

open Classical in
/-- **No recursive set is a path through the Kleene tree** — the diagonal contradiction. -/
theorem not_isBinaryPathThrough_of_recursiveSet {P : Set ℕ} (hP : RecursiveSet P) :
    ¬ IsBinaryPathThrough P kleeneTree := by
  intro hpath
  obtain ⟨cd, hcd⟩ := Nat.Partrec.Code.exists_code.mp hP
  set e₀ := Encodable.encode cd with he₀
  set b₀ : ℕ := if e₀ ∈ P then 1 else 0 with hb₀
  have hmemEval : b₀ ∈ cd.eval e₀ := by
    rw [hcd]
    simp only [charFn, hb₀, Part.mem_some_iff]
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmemEval
  set n := max k (e₀ + 1) with hn
  have hobs : diagObserved n e₀ = some b₀ := by
    have hmono : b₀ ∈ Nat.Partrec.Code.evaln n cd e₀ :=
      Nat.Partrec.Code.evaln_mono (le_max_left _ _) hk
    simpa [diagObserved, he₀, Denumerable.ofNat_encode] using hmono
  have he₀n : e₀ < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨c, hcT, hlen, hagree⟩ := hpath n
  obtain ⟨hbits, hcon⟩ := hcT
  have hne : (decodeSeq c).getD e₀ 0 ≠ b₀ % 2 :=
    hcon e₀ (by rw [hlen]; exact he₀n) b₀ (by rw [hlen]; exact hobs)
  by_cases hPe : e₀ ∈ P
  · refine hne ?_
    rw [(hagree e₀ he₀n).mpr hPe, hb₀, if_pos hPe]
  · have hnot1 : (decodeSeq c).getD e₀ 0 ≠ 1 := fun h => hPe ((hagree e₀ he₀n).mp h)
    have hle : (decodeSeq c).getD e₀ 0 ≤ 1 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlen]; exact he₀n), Option.getD_some]
      exact hbits _ (List.getElem_mem _)
    refine hne ?_
    rw [hb₀, if_neg hPe]
    omega

/-! ### The countermodel -/

/-- **REC fails weak Kőnig's lemma**: the recursive-set Turing ideal contains the Kleene
tree — internal because tree membership is recursive (`recursiveSet_kleeneTree`) — yet any
internal path would be a recursive path through it. Ambient statement; ω-scope meaning
enters only through the registered certificate. -/
theorem not_weakKonigAt_recursivePart : ¬ WeakKonigAt recursivePart := by
  intro h
  obtain ⟨P, hPpath⟩ := h ⟨kleeneTree, recursiveSet_kleeneTree⟩ isBinaryTreeCode_kleeneTree
    hasNodeAtEveryLevel_kleeneTree
  exact not_isBinaryPathThrough_of_recursiveSet P.2 hPpath

end ReverseMathlib.Omega
