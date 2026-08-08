/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.RadixCoding
import ReverseMathlib.Omega.BoundedTree
import ReverseMathlib.Omega.TreeToSystem

/-!
# `boundedTreeToSystem` and `sectionToBoundedPath` (issue #39, slice 3)

The two constructions of the `EFILCω → bounded-Kőnigω` direction, layered exactly as
`TreeToSystem`: (1) raw set/function construction; (2) relative-computability theorem;
(3) packaging as `InternalSet`/`InternalFunction`; (4) mathematical correctness.

Acceptance criteria, mirroring the binary compiler:

* level enumerations are **structural** — indices below the radix product mapped to
  mixed-radix digit lists for the bound transcript `valueTable B.eval n`, then their
  `seqCode`s filtered through the tree oracle;
* the fiber graph is Turing-reducible to the **join** of the tree and the bound graph —
  the bound enters only as the transcript oracle, the tree only as the membership oracle;
* the bonding graph is the binary compiler's `treeBondingGraph`, reused **verbatim**:
  truncation of the decoded node is tree- and bound-independent and recursive outright;
* `HasNodeAtEveryLevel` is used only in correctness proofs — no selected node enters the
  constructed data;
* the decoded path's raw graph is defined **solely** from the section graph.

Raw constructions are ambient-classical **sets** (graphs); their computability is a
separate layer-2 theorem about characteristic functions, never a claim that the Lean
definition is executable.
-/

namespace ReverseMathlib.Omega

/-- The radix list of the first `n` bound values — the per-level radices of the
structural enumeration. Equals the decoded bound transcript (`decodeSeq (valueTable β n)`). -/
def radixList (β : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map β

theorem radixList_eq_decodeSeq_valueTable (β : ℕ → ℕ) (n : ℕ) :
    radixList β n = decodeSeq (valueTable β n) := by
  rw [decodeSeq_valueTable, radixList]

theorem radixList_succ (β : ℕ → ℕ) (n : ℕ) :
    radixList β (n + 1) = radixList β n ++ [β n] := by
  rw [radixList, List.range_succ, List.map_append, List.map_cons, List.map_nil, radixList]

theorem radixList_take (β : ℕ → ℕ) (n : ℕ) :
    (radixList β (n + 1)).take n = radixList β n := by
  rw [radixList, ← List.map_take, List.take_range, show min n (n + 1) = n by omega,
    radixList]

/-- Radix-product positivity descends one level: a positive level-`n + 1` candidate count
forces a positive level-`n` candidate count. -/
theorem radixList_prod_pos {β : ℕ → ℕ} {n : ℕ} (h : 0 < (radixList β (n + 1)).prod) :
    0 < (radixList β n).prod := by
  rcases Nat.eq_zero_or_pos (radixList β n).prod with h0 | h0
  · rw [radixList_succ, List.prod_append, h0] at h
    simp at h
  · exact h0

open Classical in
/-- Layer 1 (raw): the explicit level-`n` list of a bounded tree — the `seqCode`s of all
mixed-radix digit lists for the first `n` bound values, structurally enumerated, filtered by
membership in `T`. Classical `decide` is deliberate: this is an ambient set-level
construction; its computability **relative to the tree and bound oracles** is the separate
layer-2 theorem. -/
noncomputable def boundedLevelList (T : Set ℕ) (β : ℕ → ℕ) (n : ℕ) : List ℕ :=
  ((List.range (radixList β n).prod).map
    fun i => seqCode (digitListOfIndex (radixList β n) i)).filter
    fun c => decide (c ∈ T)

/-- Layer 1 (raw): the fiber graph of the compiled inverse system — `Nat.pair n c` for `c`
the code of the level-`n` list. -/
noncomputable def boundedFiberGraph (T : Set ℕ) (β : ℕ → ℕ) : Set ℕ :=
  {p | ∃ n, p = Nat.pair n (seqCode (boundedLevelList T β n))}

/-- Everything in a bounded tree level decodes to an enumerated member of the tree. -/
theorem mem_boundedLevelList_iff {T : Set ℕ} {β : ℕ → ℕ} {n c : ℕ} :
    c ∈ boundedLevelList T β n ↔
      c ∈ T ∧ ∃ i < (radixList β n).prod, c = seqCode (digitListOfIndex (radixList β n) i) := by
  classical
  simp only [boundedLevelList, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hT⟩
    exact ⟨hT, i, hi, rfl⟩
  · rintro ⟨hT, i, hi, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hT⟩

/-! ### Layer 2: relative computability

The bonding graph needs nothing new — `recursiveSet_treeBondingGraph` is already
tree-independent. The fiber graph is Turing-reducible to the join of the tree and the bound
graph: the bound is consulted only to build the finite radix transcript, and the level codes
are then computed by a primitive recursion whose step queries the tree oracle at the
structurally enumerated candidate. -/

/-- Append one entry to a coded sequence — primitive recursive. (Private mirror of the
binary compiler's helper, which is file-private there.) -/
private theorem primrec_snocCode' : Primrec₂ fun ih x => seqCode (decodeSeq ih ++ [x]) :=
  primrec_seqCode.comp
    (Primrec₂.comp (f := fun (l m : List ℕ) => l ++ m) Primrec.list_append
      (primrec_decodeSeq.comp .fst)
      (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l) Primrec.list_cons
        .snd (.const [])))

/-- The mixed-radix candidate code is primitive recursive in the radix code and index. -/
private theorem primrec_radixCandidate :
    Primrec fun p : ℕ => seqCode (digitListOfIndex (decodeSeq p.unpair.1) p.unpair.2) :=
  primrec_seqCode.comp (Primrec₂.comp (f := digitListOfIndex) primrec_digitListOfIndex
    (primrec_decodeSeq.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

/-- The product of a decoded radix list is primitive recursive. -/
private theorem primrec_listProd : Primrec (List.prod : List ℕ → ℕ) := by
  have h : Primrec fun l : List ℕ => l.foldr (fun b acc => b * acc) 1 :=
    Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ : List ℕ => (1 : ℕ))
      (h := fun (_ : List ℕ) (p : ℕ × ℕ) => p.1 * p.2)
      Primrec.id (Primrec.const 1)
      ((Primrec.nat_mul.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂)
  exact h.of_eq fun l => List.prod_eq_foldr.symm

open Classical in
/-- Layer 2 helper (raw): the code of the level list restricted to candidate indices below
`k`, for the radix **code** `rc` — the loop state of the oracle recursion. At the full radix
product this is the full level code. -/
noncomputable def boundedLevelCodeUpTo (T : Set ℕ) (rc k : ℕ) : ℕ :=
  seqCode (((List.range k).map fun i => seqCode (digitListOfIndex (decodeSeq rc) i)).filter
    fun c => decide (c ∈ T))

open Classical in
/-- One step of the level recursion: test the `k`-th candidate against the tree. -/
theorem boundedLevelCodeUpTo_succ (T : Set ℕ) (rc k : ℕ) :
    boundedLevelCodeUpTo T rc (k + 1) =
      if seqCode (digitListOfIndex (decodeSeq rc) k) ∈ T
        then seqCode (decodeSeq (boundedLevelCodeUpTo T rc k) ++
          [seqCode (digitListOfIndex (decodeSeq rc) k)])
        else boundedLevelCodeUpTo T rc k := by
  classical
  simp only [boundedLevelCodeUpTo, List.range_succ, List.map_append, List.filter_append,
    List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, decodeSeq_seqCode]
  by_cases h : seqCode (digitListOfIndex (decodeSeq rc) k) ∈ T <;> simp [h]

/-- The full level code is the loop run to the radix product, at the bound transcript. -/
theorem seqCode_boundedLevelList (T : Set ℕ) (β : ℕ → ℕ) (n : ℕ) :
    seqCode (boundedLevelList T β n) =
      boundedLevelCodeUpTo T (valueTable β n) ((radixList β n).prod) := by
  rw [boundedLevelList, boundedLevelCodeUpTo, decodeSeq_valueTable, radixList]

/-- The level-code loop is computable relative to the tree oracle alone: a primitive
recursion whose step queries the tree at the enumerated candidate for the supplied radix
code. The tree enters **only** as the oracle; the radix code is a plain parameter. -/
theorem boundedLevelCodeUpTo_recursiveIn (T : Set ℕ) :
    Nat.RecursiveIn {charFn T}
      (fun p => Part.some (boundedLevelCodeUpTo T p.unpair.1 p.unpair.2)) := by
  classical
  have hcand : Nat.Partrec fun q => Part.some
      (seqCode (digitListOfIndex (decodeSeq q.unpair.1) q.unpair.2.unpair.1)) := by
    have hcomp := primrec_radixCandidate.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.unpair)
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    have : Primrec fun q : ℕ =>
        seqCode (digitListOfIndex (decodeSeq q.unpair.1) q.unpair.2.unpair.1) :=
      hcomp.of_eq fun q => by rw [Nat.unpair_pair]
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hid : Nat.RecursiveIn {charFn T} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have horacle : Nat.RecursiveIn {charFn T} fun q =>
      charFn T (seqCode (digitListOfIndex (decodeSeq q.unpair.1) q.unpair.2.unpair.1)) :=
    recursiveIn_comp_partrec (Nat.RecursiveIn.oracle (O := {charFn T}) _ rfl) hcand
  have hpair := hid.pair horacle
  have hpost : Nat.Partrec fun m => Part.some (if m.unpair.2 = 1
      then seqCode (decodeSeq m.unpair.1.unpair.2.unpair.2 ++
        [seqCode (digitListOfIndex (decodeSeq m.unpair.1.unpair.1)
          m.unpair.1.unpair.2.unpair.1)])
      else m.unpair.1.unpair.2.unpair.2) := by
    have hq : Primrec fun m : ℕ => m.unpair.1 := Primrec.fst.comp Primrec.unpair
    have hi : Primrec fun m : ℕ => m.unpair.1.unpair.2.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hq)))
    have hcomp' := primrec_radixCandidate.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp hq))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
        (Primrec.unpair.comp hq)))))
    have hcand' : Primrec fun m : ℕ =>
        seqCode (digitListOfIndex (decodeSeq m.unpair.1.unpair.1)
          m.unpair.1.unpair.2.unpair.1) :=
      hcomp'.of_eq fun m => by rw [Nat.unpair_pair]
    have hval : Primrec fun m : ℕ => if m.unpair.2 = 1
        then seqCode (decodeSeq m.unpair.1.unpair.2.unpair.2 ++
          [seqCode (digitListOfIndex (decodeSeq m.unpair.1.unpair.1)
            m.unpair.1.unpair.2.unpair.1)])
        else m.unpair.1.unpair.2.unpair.2 :=
      Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 1))
        (Primrec₂.comp (f := fun ih x => seqCode (decodeSeq ih ++ [x]))
          primrec_snocCode' hi hcand')
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
    simp [boundedLevelCodeUpTo]
  | succ y ih =>
    rw [← Nat.succ_eq_add_one]
    dsimp only
    rw [ih]
    simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
      Part.map_some, Nat.unpair_pair, boundedLevelCodeUpTo_succ]
    by_cases hmem : seqCode (digitListOfIndex (decodeSeq a) y) ∈ T
    · rw [if_pos hmem, if_pos rfl, if_pos hmem]
    · rw [if_neg hmem, if_neg (by omega), if_neg hmem]

/-- Membership in the fiber graph is an equation against the level code. -/
theorem mem_boundedFiberGraph_iff {T : Set ℕ} {β : ℕ → ℕ} {p : ℕ} :
    p ∈ boundedFiberGraph T β ↔
      p.unpair.2 = seqCode (boundedLevelList T β p.unpair.1) := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [Nat.unpair_pair]
  · intro h
    exact ⟨p.unpair.1, by rw [← h, Nat.pair_unpair]⟩

/-- **Layer 2, `boundedTreeToSystem`**: the fiber graph is Turing-reducible to the join of
the tree and the bound graph. The bound is consulted only through the finite radix
transcript (`valueTable`, along `right_le_joinSet`); the tree is consulted only by the level
loop (along `left_le_joinSet`). -/
theorem boundedFiberGraph_le_join {Ω : OmegaPart} (T : Set ℕ) (B : InternalFunction Ω) :
    boundedFiberGraph T B.eval ≤ᵀ joinSet T B.graph.1 := by
  classical
  have hloop : Nat.RecursiveIn {charFn (joinSet T B.graph.1)}
      (fun q => Part.some (boundedLevelCodeUpTo T q.unpair.1 q.unpair.2)) :=
    recursiveIn_of_turingReducible (boundedLevelCodeUpTo_recursiveIn T)
      (left_le_joinSet _ _)
  have hEval : Nat.RecursiveIn {charFn (joinSet T B.graph.1)}
      (fun k => Part.some (B.eval k)) :=
    recursiveIn_of_turingReducible B.eval_recursiveIn_graph (right_le_joinSet _ _)
  have htable : Nat.RecursiveIn {charFn (joinSet T B.graph.1)}
      (fun p => Part.some (valueTable B.eval p.unpair.1)) :=
    recursiveIn_comp_primrec (valueTable_recursiveIn hEval)
      (Primrec.fst.comp Primrec.unpair)
  have hpairup : Primrec fun rc : ℕ => Nat.pair rc (decodeSeq rc).prod :=
    Primrec₂.natPair.comp Primrec.id (primrec_listProd.comp primrec_decodeSeq)
  have harg := recursiveIn_comp_total (recursiveIn_of_primrec hpairup) htable
  have hfull : Nat.RecursiveIn {charFn (joinSet T B.graph.1)}
      (fun p => Part.some (boundedLevelCodeUpTo T (valueTable B.eval p.unpair.1)
        ((decodeSeq (valueTable B.eval p.unpair.1)).prod))) :=
    (recursiveIn_comp_total hloop harg).of_eq fun p => by simp [Nat.unpair_pair]
  have hpaired := (((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq
    (fun (_ : ℕ) => rfl) :
      Nat.RecursiveIn {charFn (joinSet T B.graph.1)} fun q => Part.some q).pair hfull
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1.unpair.2 = m.unpair.2 then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1.unpair.2 = m.unpair.2 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpaired).of_eq fun p => ?_
  have hlevel : boundedLevelCodeUpTo T (valueTable B.eval p.unpair.1)
      ((decodeSeq (valueTable B.eval p.unpair.1)).prod)
        = seqCode (boundedLevelList T B.eval p.unpair.1) := by
    rw [seqCode_boundedLevelList, radixList_eq_decodeSeq_valueTable]
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases h : p ∈ boundedFiberGraph T B.eval
  · rw [if_pos (by rw [hlevel]; exact mem_boundedFiberGraph_iff.mp h), if_pos h]
  · rw [if_neg (fun hc => h (mem_boundedFiberGraph_iff.mpr (by rw [← hlevel]; exact hc))),
      if_neg h]

/-! ### Layer 3: internal packaging — no tree hypotheses

Totality and single-valuedness of the fiber graph hold for an **arbitrary** set `T` and
bound function `B`; Ω-membership comes from ideal closure (join then reducibility) applied
to the layer-2 theorem. The mathematical bounded-tree properties enter only in layer 4. -/

/-- The fiber enumerator of an internal bounded tree, as an internal graph-coded
function — internal by ideal closure under join and the layer-2 reduction. -/
def boundedFiberFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω) (T : Ω.InternalSet)
    (B : InternalFunction Ω) : InternalFunction Ω where
  graph := ⟨boundedFiberGraph T.1 B.eval,
    h.mem_of_reducible (h.join T.2 B.graph.2) (boundedFiberGraph_le_join T.1 B)⟩
  total := fun n => ⟨seqCode (boundedLevelList T.1 B.eval n), ⟨n, rfl⟩⟩
  singleValued := fun n y y' hy hy' => by
    obtain ⟨m, hm⟩ := hy
    obtain ⟨m', hm'⟩ := hy'
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    obtain ⟨h1, rfl⟩ := Nat.pair_eq_pair.mp hm'
    rw [h1]

/-! ### Layer 4: assembling the inverse system

The enumeration laws the assembly needs — injectivity, completeness, and the truncation
normal form — live in `ReverseMathlib.Omega.RadixCoding`. Completeness plus the supplied
bound certificate is what lets `HasNodeAtEveryLevel` supply fiber nonemptiness purely
through a lemma, so no chosen node is ever stored in data. -/

/-- The level enumeration is duplicate-free: range nodup → injective enumeration →
injective coding → nodup map → nodup filter. -/
theorem boundedLevelList_nodup (T : Set ℕ) (β : ℕ → ℕ) (n : ℕ) :
    (boundedLevelList T β n).Nodup := by
  classical
  refine List.Nodup.filter _ (List.Nodup.map_on ?_ List.nodup_range)
  intro i hi i' hi' hEq
  exact digitListOfIndex_injOn (List.mem_range.mp hi) (List.mem_range.mp hi')
    (seqCode_injective hEq)

/-- A positionally bounded list of the right length is entrywise below the radix list. -/
private theorem forall₂_lt_radixList {l : List ℕ} {β : ℕ → ℕ} {n : ℕ}
    (hlen : l.length = n) (hb : ∀ i < n, l.getD i 0 < β i) :
    List.Forall₂ (· < ·) l (radixList β n) := by
  refine List.forall₂_iff_get.mpr ⟨by simp [radixList, hlen], fun i h₁ h₂ => ?_⟩
  have hi : i < n := hlen ▸ h₁
  have hg := hb i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some] at hg
  simpa [radixList, List.get_eq_getElem] using hg

/-- **Layer 4: `boundedTreeToSystem`.** The bounded-tree data and hypotheses enter only
here: the supplied bound certificate plus enumeration completeness turn
`HasNodeAtEveryLevel` into fiber nonemptiness, and prefix closure supplies `bonding_mem`
through the truncation normal form — no selected node is ever stored in the constructed
data. The bonding is the binary compiler's truncation function, reused verbatim. -/
def boundedTreeToSystem {Ω : OmegaPart} (h : IsTuringIdeal Ω) (T : InternalBoundedTree Ω)
    (hlev : HasNodeAtEveryLevel T.tree.1) : InternalInverseSystem Ω where
  fibers := boundedFiberFunction h T.tree T.bound
  bonding := treeBondingFunction h
  fiber_nodup := fun n c hc => by
    obtain ⟨m, hm⟩ := hc
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    rw [decodeSeq_seqCode]
    exact boundedLevelList_nodup T.tree.1 T.bound.eval n
  fiber_nonempty := fun n c hc => by
    obtain ⟨m, hm⟩ := hc
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hm
    rw [decodeSeq_seqCode]
    obtain ⟨c₀, hc₀T, hlen⟩ := hlev n
    have hfa : List.Forall₂ (· < ·) (decodeSeq c₀) (radixList T.bound.eval n) :=
      forall₂_lt_radixList hlen fun i hi =>
        T.entry_lt_bound c₀ hc₀T i (T.bound.eval i) (by rw [hlen]; exact hi)
          (T.bound.pair_eval_mem i)
    obtain ⟨i, hi, hdi⟩ := exists_digitListOfIndex hfa
    have hmem : c₀ ∈ boundedLevelList T.tree.1 T.bound.eval n := by
      refine mem_boundedLevelList_iff.mpr ⟨hc₀T, i, hi, ?_⟩
      conv_lhs => rw [← seqCode_decodeSeq c₀]
      rw [← hdi]
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
    obtain ⟨hxT, i, hi, rfl⟩ := mem_boundedLevelList_iff.mp hx
    have hpos : 0 < (radixList T.bound.eval n).prod :=
      radixList_prod_pos (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
    refine mem_boundedLevelList_iff.mpr
      ⟨?_, i % (radixList T.bound.eval n).prod, Nat.mod_lt _ hpos, ?_⟩
    · rw [h1]
      exact T.prefix_closed _ hxT n
    · rw [h1, decodeSeq_seqCode, digitListOfIndex_take, radixList_take]

/-! ### `sectionToBoundedPath`: the decoded path

The raw graph is the **specification**, mentioning only the section graph: position `i`
maps to the entry the level-`i + 1` section value carries at position `i`. The compiled
system first appears in path correctness. -/

/-- Layer 1 (raw, the specification): the graph of the decoded path — `Nat.pair i v` for
`v` the entry at position `i` of the level-`i + 1` section value. Mentions **only** the
section graph. -/
def sectionBoundedPathGraph {Ω : OmegaPart} (s : InternalFunction Ω) : Set ℕ :=
  {q | ∃ c, s.MapsTo (q.unpair.1 + 1) c ∧ (decodeSeq c).getD q.unpair.1 0 = q.unpair.2}

/-- **Iterated section coherence** for the bounded compiler: a section value at any lower
level is the truncation of the value at any higher level. All intermediate-value selection
happens inside this proof. -/
theorem bounded_section_value_take {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {T : InternalBoundedTree Ω} {hlev : HasNodeAtEveryLevel T.tree.1}
    {s : InternalFunction Ω} (hs : (boundedTreeToSystem h T hlev).IsSection s) :
    ∀ {n k c c'}, k ≤ n → s.MapsTo n c → s.MapsTo k c' →
      c' = seqCode ((decodeSeq c).take k) := by
  -- Same-level normal form: every section value is a length-`level` node code.
  have hself : ∀ {m cm}, s.MapsTo m cm → cm = seqCode ((decodeSeq cm).take m) := by
    intro m cm hcm
    have hfib : (boundedTreeToSystem h T hlev).fibers.MapsTo m
        (seqCode (boundedLevelList T.tree.1 T.bound.eval m)) := ⟨m, rfl⟩
    have hmem := hs.1 m _ cm hfib hcm
    rw [decodeSeq_seqCode] at hmem
    obtain ⟨-, i, -, rfl⟩ := mem_boundedLevelList_iff.mp hmem
    rw [decodeSeq_seqCode, List.take_of_length_le (by simp [radixList])]
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

/-- **Layer 2, `sectionToBoundedPath`**: the decoded path graph is Turing-reducible to the
section graph — this theorem mentions **only** `s.graph`; no tree appears. Unique graph
lookup at level `i + 1` followed by a primitive recursive entry inspection. -/
theorem sectionBoundedPathGraph_le_graph {Ω : OmegaPart} (s : InternalFunction Ω) :
    sectionBoundedPathGraph s ≤ᵀ s.graph.1 := by
  classical
  have hsucc : Nat.Partrec fun q => Part.some (q.unpair.1 + 1) := by
    have : Primrec fun q : ℕ => q.unpair.1 + 1 :=
      Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have heval := recursiveIn_comp_partrec s.eval_recursiveIn_graph hsucc
  have hid : Nat.RecursiveIn {charFn s.graph.1} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpost : Nat.Partrec fun m => Part.some
      (if (decodeSeq m.unpair.2).getD m.unpair.1.unpair.1 0 = m.unpair.1.unpair.2
        then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if (decodeSeq m.unpair.2).getD m.unpair.1.unpair.1 0 = m.unpair.1.unpair.2
          then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
          (Primrec.snd.comp Primrec.unpair)
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp (hid.pair heval)).of_eq fun q => ?_
  have hiff : q ∈ sectionBoundedPathGraph s ↔
      (decodeSeq (s.eval (q.unpair.1 + 1))).getD q.unpair.1 0 = q.unpair.2 := by
    constructor
    · rintro ⟨c, hc, hent⟩
      have : s.eval (q.unpair.1 + 1) = c := s.mapsTo_iff_eval_eq.mp hc
      rwa [this]
    · exact fun hent => ⟨s.eval (q.unpair.1 + 1), s.pair_eval_mem _, hent⟩
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases hent : (decodeSeq (s.eval (q.unpair.1 + 1))).getD q.unpair.1 0 = q.unpair.2
  · rw [if_pos hent, if_pos (hiff.mpr hent)]
  · rw [if_neg hent, if_neg fun hc => hent (hiff.mp hc)]

/-- Layer 3: the decoded path as an internal graph-coded function — ideal closure on the
layer-2 reducibility; totality and single-valuedness come from the section function alone.
No tree hypotheses; the tree first appears in path correctness. -/
def sectionBoundedPathFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (s : InternalFunction Ω) : InternalFunction Ω where
  graph := ⟨sectionBoundedPathGraph s,
    h.mem_of_reducible s.graph.2 (sectionBoundedPathGraph_le_graph s)⟩
  total := fun i => by
    obtain ⟨c, hc⟩ := s.total (i + 1)
    exact ⟨(decodeSeq c).getD i 0, c, by rwa [Nat.unpair_pair], by rw [Nat.unpair_pair]⟩
  singleValued := fun i v v' hv hv' => by
    obtain ⟨c, hc, hval⟩ := hv
    obtain ⟨c', hc', hval'⟩ := hv'
    simp only [Nat.unpair_pair] at hc hc' hval hval'
    rw [← hval, ← hval', s.singleValued _ c c' hc hc']

/-- The decoded path's values, relationally: `MapsTo i v` holds exactly when the
level-`i + 1` section value carries entry `v` at position `i`. -/
theorem sectionBoundedPathFunction_mapsTo_iff {Ω : OmegaPart} {h : IsTuringIdeal Ω}
    {s : InternalFunction Ω} {i v : ℕ} :
    (sectionBoundedPathFunction h s).MapsTo i v ↔
      ∃ c, s.MapsTo (i + 1) c ∧ (decodeSeq c).getD i 0 = v := by
  constructor
  · rintro ⟨c, hc, hval⟩
    simp only [Nat.unpair_pair] at hc hval
    exact ⟨c, hc, hval⟩
  · rintro ⟨c, hc, hval⟩
    exact ⟨c, by rwa [Nat.unpair_pair], by rwa [Nat.unpair_pair]⟩

end ReverseMathlib.Omega
