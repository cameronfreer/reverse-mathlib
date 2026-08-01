/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Finite
import ReverseMathlib.Omega.Hall
import ReverseMathlib.Omega.TreeToSystem

/-!
# Countable Hall from EFILC at a second-order part (issue #22, slice 4)

The ω-internal walking slice, mirroring the ambient
`ReverseMathlib.Slice.countableHall_of_finiteInverseLimitCompactness` through the
demonstrated pipeline: an internal Hall family compiles to an internal inverse system of
injective partial transversals (`hallToSystem`), EFILCω supplies an internal section, and
the section decodes to an injective internal transversal
(`sectionTransversalFunction`) — giving `countableHallAt_of_efilcAt`.

**Fine dependencies are enforced in the types**, following the decoder pattern:

* the fiber compiler takes only the candidate **enumerator** (`enum : InternalFunction Ω`),
  so its reduction states exactly `hallFiberGraph enum ≤ᵀ enum.graph.1` — the candidate
  **relation** cannot enter: it is not in scope, and appears only in the correctness
  theorem (through `mem_iff`);
* the transversal decoder takes only the **section**, so its reduction states exactly
  `sectionTransversalGraph s ≤ᵀ s.graph.1`;
* the bonding maps are truncation — literally the reused `treeBondingFunction`, recursive
  and internal to every Turing ideal.

The computability argument is again *finite oracle transcript, then pure verifier*: the
only unbounded-search channel is enumerator lookup, invoked finitely many times,
input-dependently — once per level below the queried one — to build the candidate table
(a `valueTable`); everything after transcript construction is pure primitive-recursive
computation. Injective tuples are enumerated *directly* (each level extends only by unused
candidates), so no duplicate-freeness test is ever computed.

Level nonemptiness is the one reuse of mathlib's Hall machinery: the **finite** marriage
theorem (`Finset.all_card_le_biUnion_card_iff_existsInjective'`) — reused, not reinvented,
exactly as in the ambient slice; the infinite Hall theorem is excluded at import level and
by the route gates in `scripts/MetaSmoke.lean`.
-/

assert_not_exists Finset.all_card_le_biUnion_card_iff_exists_injective

namespace ReverseMathlib.Omega

/-! ### Layer 1: the pure table-driven tuple enumeration

A candidate table is a coded list of coded candidate lists. Everything here is a total
function of raw naturals, so the whole enumeration is primitive recursive. -/

/-- Membership on raw lists as a Boolean, in structural-recursion form. -/
private def memB (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: t => decide (b = a) || memB a t

private theorem memB_eq_true {a : ℕ} {l : List ℕ} : memB a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons b t ih =>
    simp only [memB, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr_left eq_comm

private theorem memB_eq_false {a : ℕ} {l : List ℕ} : memB a l = false ↔ a ∉ l := by
  rw [Bool.eq_false_iff]
  exact not_congr memB_eq_true

/-- Row `k` of a candidate table — the level-`k` candidate list; `[]` when absent. -/
def hallCandRow (tbl k : ℕ) : List ℕ :=
  decodeSeq ((decodeSeq tbl).getD k 0)

/-- All **injective** tuples whose `i`-th entry is a candidate from row `i`: each level
extends only by candidates not already used, so injectivity holds by construction and no
duplicate-freeness test is ever computed. -/
def hallTuples (tbl : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 =>
      (hallTuples tbl n).flatMap fun t =>
        ((hallCandRow tbl n).filter fun y => !(memB y t)).map fun y => t ++ [y]

/-- Membership characterization of the enumeration: exactly the length-`n` injective
tuples with in-row entries. -/
theorem mem_hallTuples (tbl : ℕ) : ∀ (n : ℕ) (t : List ℕ),
    t ∈ hallTuples tbl n ↔
      t.length = n ∧ (∀ i, (hi : i < t.length) → t[i] ∈ hallCandRow tbl i) ∧ t.Nodup := by
  intro n
  induction n with
  | zero =>
    intro t
    simp only [hallTuples, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, fun i hi => absurd hi (by simp), List.nodup_nil⟩
    · rintro ⟨hlen, -, -⟩
      exact List.eq_nil_of_length_eq_zero hlen
  | succ n ih =>
    intro t
    simp only [hallTuples, List.mem_flatMap, List.mem_map, List.mem_filter,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · rintro ⟨t', ht', y, ⟨hy, hyB⟩, rfl⟩
      obtain ⟨hlen, hmem, hnd⟩ := (ih t').mp ht'
      have hynot : y ∉ t' := memB_eq_false.mp hyB
      refine ⟨by simp [hlen], fun i hi => ?_, ?_⟩
      · rcases Nat.lt_or_ge i t'.length with h | h
        · rw [List.getElem_append_left h]
          exact hmem i h
        · have hieq : i = t'.length := by
            have h2 : i < t'.length + 1 := by simpa using hi
            omega
          subst hieq
          have hval : (t' ++ [y])[t'.length]'hi = y := by
            have h3 : (t' ++ [y])[t'.length]? = some y := List.getElem?_concat_length
            rw [List.getElem?_eq_getElem hi] at h3
            exact Option.some_injective _ h3
          rw [hval, hlen]
          exact hy
      · exact ((List.perm_append_singleton y t').nodup_iff).mpr
          (List.nodup_cons.mpr ⟨hynot, hnd⟩)
    · rintro ⟨hlen, hmem, hnd⟩
      have hn : n < t.length := by omega
      have hdrop : t.drop n = [t[n]] := by
        rw [List.drop_eq_getElem_cons hn]
        have : t.drop (n + 1) = [] := List.drop_eq_nil_of_le (by omega)
        rw [this]
      have htake : t.take n ++ [t[n]] = t := by
        rw [← hdrop, List.take_append_drop]
      have hnotmem : t[n] ∉ t.take n := by
        intro hc
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hc
        have hj' : j < n := by simpa [List.length_take, hlen] using hj
        rw [List.getElem_take] at hjeq
        have : j = n := hnd.getElem_inj_iff.mp hjeq
        omega
      refine ⟨t.take n, (ih _).mpr ⟨?_, ?_, hnd.sublist (List.take_sublist n t)⟩,
        t[n], ⟨?_, memB_eq_false.mpr hnotmem⟩, htake⟩
      · rw [List.length_take, hlen]
        omega
      · intro i hi
        have hi' : i < n := by simpa [List.length_take, hlen] using hi
        rw [List.getElem_take]
        exact hmem i (by omega)
      · exact hmem n hn

/-- The enumeration lists distinct tuples, provided the rows are duplicate-free. -/
theorem hallTuples_nodup (tbl : ℕ) (hrows : ∀ k, (hallCandRow tbl k).Nodup) :
    ∀ n, (hallTuples tbl n).Nodup := by
  intro n
  induction n with
  | zero => exact List.nodup_singleton []
  | succ n ih =>
    rw [hallTuples, List.nodup_flatMap]
    constructor
    · intro t _
      refine List.Nodup.map (fun y y' h => ?_) ((hrows n).filter _)
      have := List.append_cancel_left h
      simpa using this
    · refine ih.imp_of_mem fun {t t'} ht ht' hne l hl hl' => ?_
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hl
      obtain ⟨y', -, heq⟩ := List.mem_map.mp hl'
      have hlen := ((mem_hallTuples tbl n t).mp ht).1
      have hlen' := ((mem_hallTuples tbl n t').mp ht').1
      apply hne
      have htake := congrArg (fun l => List.take n l) heq.symm
      simpa [List.take_left', hlen, hlen'] using htake

/-! #### Primitive recursiveness of the enumeration -/

private theorem filter_not_map_eq_flatMap (q : ℕ → Bool) (g : ℕ → List ℕ) :
    ∀ l : List ℕ, ((l.filter fun a => !(q a)).map g) =
      l.flatMap fun a => if q a then [] else [g a] := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => cases hq : q a <;> simp [hq, ih]

private theorem hallTuples_eq_nat_rec (tbl n : ℕ) :
    hallTuples tbl n = Nat.rec (motive := fun _ => List (List ℕ)) [[]]
      (fun m IH => IH.flatMap fun t =>
        (hallCandRow tbl m).flatMap fun y => if memB y t then [] else [t ++ [y]]) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hallTuples, ih]
    simp only [filter_not_map_eq_flatMap]

theorem primrec_hallCandRow : Primrec₂ hallCandRow :=
  primrec_decodeSeq.comp
    (Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
      Primrec.fst Primrec.snd)

private theorem memB_eq_foldr (a : ℕ) (l : List ℕ) :
    memB a l = l.foldr (fun b acc => decide (b = a) || acc) false := by
  induction l with
  | nil => rfl
  | cons b t ih => rw [List.foldr_cons, ← ih]; rfl

private theorem primrec_memB : Primrec₂ memB := by
  have h : Primrec fun p : ℕ × List ℕ =>
      p.2.foldr (fun b acc => decide (b = p.1) || acc) false :=
    Primrec.list_foldr (f := fun p : ℕ × List ℕ => p.2)
      (g := fun _ : ℕ × List ℕ => false)
      (h := fun (p : ℕ × List ℕ) (q : ℕ × Bool) => decide (q.1 = p.1) || q.2)
      Primrec.snd (Primrec.const false)
      ((Primrec.or.comp
        ((Primrec.eq.comp (Primrec.fst.comp .snd) (Primrec.fst.comp .fst)).decide)
        (Primrec.snd.comp .snd)).to₂)
  exact h.of_eq fun p => (memB_eq_foldr p.1 p.2).symm

theorem primrec_hallTuples : Primrec₂ hallTuples := by
  have hbody : Primrec fun v : ((ℕ × ℕ × List (List ℕ)) × List ℕ) × ℕ =>
      if memB v.2 v.1.2 then [] else [v.1.2 ++ [v.2]] :=
    Primrec.ite
      (Primrec.eq.comp
        (Primrec₂.comp (f := memB) primrec_memB Primrec.snd
          (Primrec.snd.comp Primrec.fst))
        (Primrec.const true))
      (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec₂.comp (f := fun (l : List ℕ) (a : ℕ) => l ++ [a]) Primrec.list_concat
          (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.const []))
  have hinner : Primrec₂ fun (w : (ℕ × ℕ × List (List ℕ)) × List ℕ) (y : ℕ) =>
      if memB y w.2 then [] else [w.2 ++ [y]] := hbody.to₂
  have hrow : Primrec fun w : (ℕ × ℕ × List (List ℕ)) × List ℕ =>
      hallCandRow w.1.1 w.1.2.1 :=
    Primrec₂.comp (f := hallCandRow) primrec_hallCandRow (Primrec.fst.comp .fst)
      (Primrec.fst.comp (Primrec.snd.comp .fst))
  have hg : Primrec₂ fun (z : ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
      (hallCandRow z.1 z.2.1).flatMap fun y => if memB y t then [] else [t ++ [y]] :=
    Primrec.list_flatMap
      (f := fun w : (ℕ × ℕ × List (List ℕ)) × List ℕ => hallCandRow w.1.1 w.1.2.1)
      (g := fun (w : (ℕ × ℕ × List (List ℕ)) × List ℕ) (y : ℕ) =>
        if memB y w.2 then [] else [w.2 ++ [y]])
      hrow hinner
  have hstep : Primrec₂ fun (tbl : ℕ) (q : ℕ × List (List ℕ)) =>
      q.2.flatMap fun t =>
        (hallCandRow tbl q.1).flatMap fun y => if memB y t then [] else [t ++ [y]] :=
    Primrec.list_flatMap (f := fun z : ℕ × ℕ × List (List ℕ) => z.2.2)
      (g := fun (z : ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
        (hallCandRow z.1 z.2.1).flatMap fun y => if memB y t then [] else [t ++ [y]])
      (Primrec.snd.comp .snd) hg
  exact (Primrec.nat_rec (Primrec.const [[]]) hstep).of_eq fun tbl n =>
    (hallTuples_eq_nat_rec tbl n).symm

/-- The coded level: the enumerated injective tuples, each coded, the list coded. -/
def hallFiberCodeT (tbl n : ℕ) : ℕ :=
  seqCode ((hallTuples tbl n).map seqCode)

theorem primrec_hallFiberCodeT : Primrec₂ hallFiberCodeT :=
  primrec_seqCode.comp
    (Primrec.list_map (f := fun p : ℕ × ℕ => hallTuples p.1 p.2)
      (g := fun (_ : ℕ × ℕ) (t : List ℕ) => seqCode t)
      (Primrec₂.comp (f := hallTuples) primrec_hallTuples Primrec.fst Primrec.snd)
      (primrec_seqCode.comp Primrec.snd).to₂)

/-! ### The ideal candidate table, and the fiber function on the enumerator alone

The **fine dependency is the type**: everything below takes only the candidate enumerator
`enum : InternalFunction Ω`. The candidate relation of a Hall family cannot enter — it is
not in scope — and appears only in the correctness theorem at the end of this file. -/

/-- The candidate transcript up to level `L`: row `k` is the level-`k` candidate-list
code. A `valueTable`, so it is a finite oracle computation against the enumerator. -/
noncomputable def hallCandTable {Ω : OmegaPart} (enum : InternalFunction Ω) (L : ℕ) : ℕ :=
  valueTable enum.eval L

theorem hallCandRow_candTable {Ω : OmegaPart} (enum : InternalFunction Ω) {L k : ℕ}
    (h : k < L) : hallCandRow (hallCandTable enum L) k = decodeSeq (enum.eval k) := by
  rw [hallCandRow, hallCandTable, decodeSeq_valueTable, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range h, Option.map_some, Option.getD_some]

/-- Level `n` of the compiled system, as a tuple list: the injective partial transversals
on `{0, …, n - 1}` with entries from the enumerated candidate lists. -/
noncomputable def hallLevel {Ω : OmegaPart} (enum : InternalFunction Ω) (n : ℕ) :
    List (List ℕ) :=
  hallTuples (hallCandTable enum n) n

theorem mem_hallLevel {Ω : OmegaPart} (enum : InternalFunction Ω) {n : ℕ} {t : List ℕ} :
    t ∈ hallLevel enum n ↔ t.length = n ∧
      (∀ i, (hi : i < t.length) → t[i] ∈ decodeSeq (enum.eval i)) ∧ t.Nodup := by
  rw [hallLevel, mem_hallTuples]
  refine and_congr_right fun hlen => and_congr_left fun _ => ?_
  refine forall_congr' fun i => ?_
  refine forall_congr' fun hi => ?_
  rw [hallCandRow_candTable enum (by omega)]

/-- Layer 1 (raw): the level-`n` fiber code of the compiled system. -/
noncomputable def hallFiberCode {Ω : OmegaPart} (enum : InternalFunction Ω) (n : ℕ) : ℕ :=
  hallFiberCodeT (hallCandTable enum n) n

theorem decodeSeq_hallFiberCode {Ω : OmegaPart} (enum : InternalFunction Ω) (n : ℕ) :
    decodeSeq (hallFiberCode enum n) = (hallLevel enum n).map seqCode := by
  rw [hallFiberCode, hallFiberCodeT, decodeSeq_seqCode, hallLevel]

/-- The graph of the fiber compiler, as a set of `Nat.pair` codes. -/
def hallFiberGraph {Ω : OmegaPart} (enum : InternalFunction Ω) : Set ℕ :=
  {m | hallFiberCode enum m.unpair.1 = m.unpair.2}

theorem isGraphOf_hallFiberGraph {Ω : OmegaPart} (enum : InternalFunction Ω) :
    IsGraphOf (hallFiberGraph enum) (hallFiberCode enum) := fun x y => by
  simp [hallFiberGraph, Nat.unpair_pair, Set.mem_setOf_eq]

/-! ### Layer 2: the fiber compiler reduces to the enumerator graph -/

/-- The fiber codes are computable from the enumerator graph: build the candidate
transcript (the only oracle use — enumerator lookup, once per level below the queried
one), then compute the level purely. -/
theorem hallFiberCode_recursiveIn {Ω : OmegaPart} (enum : InternalFunction Ω) :
    Nat.RecursiveIn {charFn enum.graph.1}
      fun n => Part.some (hallFiberCode enum n) := by
  have htab : Nat.RecursiveIn {charFn enum.graph.1}
      fun L => Part.some (hallCandTable enum L) :=
    valueTable_recursiveIn enum.eval_recursiveIn_graph
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hpost : Primrec fun z : ℕ => hallFiberCodeT z.unpair.1 z.unpair.2 :=
    Primrec₂.comp (f := hallFiberCodeT) primrec_hallFiberCodeT hfst hsnd
  exact (recursiveIn_comp_total (recursiveIn_of_primrec hpost)
    (recursiveIn_pair_total htab (recursiveIn_of_primrec Primrec.id))).of_eq fun n => by
      simp only [Nat.unpair_pair, id_eq, hallFiberCode]

/-- **The fiber compiler's reduction**: the compiled fiber graph is Turing reducible to
the enumerator graph alone — the exact fine dependency, stated on exactly the data the
compiler's type admits. -/
theorem hallFiberGraph_le_enum {Ω : OmegaPart} (enum : InternalFunction Ω) :
    hallFiberGraph enum ≤ᵀ enum.graph.1 := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hval := recursiveIn_comp_primrec (hallFiberCode_recursiveIn enum) hfst
  have hpair := recursiveIn_pair_total hval (recursiveIn_of_primrec Primrec.id)
  have hpost : Primrec fun z : ℕ => if z.unpair.1 = z.unpair.2.unpair.2 then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hfst (hsnd.comp hsnd)) (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun m => ?_
  simp only [Nat.unpair_pair, id_eq, charFn]
  by_cases hm : hallFiberCode enum m.unpair.1 = m.unpair.2
  · rw [if_pos hm, if_pos (show m ∈ hallFiberGraph enum from hm)]
  · rw [if_neg hm, if_neg (show m ∉ hallFiberGraph enum from hm)]

/-! ### Layer 3: internal packaging -/

/-- The compiled fiber enumerator as an internal graph-coded function — internal by
Turing-ideal closure under the candidate enumerator's graph. -/
def hallFiberFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (enum : InternalFunction Ω) : InternalFunction Ω where
  graph := ⟨hallFiberGraph enum,
    h.mem_of_reducible enum.graph.2 (hallFiberGraph_le_enum enum)⟩
  total x := ⟨hallFiberCode enum x, (isGraphOf_hallFiberGraph enum x _).mpr rfl⟩
  singleValued x y y' hy hy' :=
    ((isGraphOf_hallFiberGraph enum x y).mp hy).symm.trans
      ((isGraphOf_hallFiberGraph enum x y').mp hy')

/-- The relational surface of the packaged fiber compiler. -/
theorem hallFiberFunction_mapsTo_iff {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (enum : InternalFunction Ω) {n c : ℕ} :
    (hallFiberFunction h enum).MapsTo n c ↔ hallFiberCode enum n = c :=
  isGraphOf_hallFiberGraph enum n c

/-! ### Layer 4: assembling the inverse system

Only here does the full `InternalHallFamily` enter: `enum_nodup` gives fiber
duplicate-freeness, the marriage condition gives fiber nonemptiness through mathlib's
**finite** Hall theorem, and the injective-tuple characterization gives `bonding_mem`
under truncation. The bonding maps are the reused `treeBondingFunction`. -/

private theorem decodeSeq_zero : decodeSeq 0 = [] := by
  rw [show (0 : ℕ) = seqCode [] from rfl, decodeSeq_seqCode]

private theorem hallCandTable_rows_nodup {Ω : OmegaPart} (H : InternalHallFamily Ω)
    (n k : ℕ) : (hallCandRow (hallCandTable H.enum n) k).Nodup := by
  rcases Nat.lt_or_ge k n with hk | hk
  · rw [hallCandRow_candTable H.enum hk]
    exact H.enum_nodup k _ (H.enum.pair_eval_mem k)
  · rw [hallCandRow, hallCandTable, List.getD_eq_getElem?_getD, List.getElem?_eq_none,
      Option.getD_none, decodeSeq_zero]
    · exact List.nodup_nil
    · rw [decodeSeq_valueTable, List.length_map, List.length_range]
      omega

/-- The pure finite-Hall step, over an abstract candidate-list family: the marriage
condition yields an injective length-`n` tuple of in-list candidates. The one reuse of
mathlib's Hall machinery (`Finset.all_card_le_biUnion_card_iff_existsInjective'`), exactly
as in the ambient slice. No matching is selected: the witness tuple is produced
directly. -/
private theorem exists_hall_tuple (cand : ℕ → List ℕ)
    (hmar : ∀ s : Finset ℕ, s.card ≤ (s.biUnion fun k => (cand k).toFinset).card)
    (n : ℕ) : ∃ t : List ℕ, t.length = n ∧
      (∀ i, (hi : i < t.length) → t[i] ∈ cand i) ∧ t.Nodup := by
  have hall : ∀ s : Finset (Fin n),
      s.card ≤ (s.biUnion fun i => (cand i.1).toFinset).card := by
    intro s
    have himg : ((s.image Fin.val).biUnion fun k => (cand k).toFinset) =
        s.biUnion fun i => (cand i.1).toFinset :=
      Finset.image_biUnion
    calc s.card = (s.image Fin.val).card :=
          (Finset.card_image_of_injective s Fin.val_injective).symm
      _ ≤ ((s.image Fin.val).biUnion fun k => (cand k).toFinset).card := hmar _
      _ = (s.biUnion fun i => (cand i.1).toFinset).card := by rw [himg]
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      fun i : Fin n => (cand i.1).toFinset).mp hall
  refine ⟨List.ofFn f, by simp, fun i hi => ?_, List.nodup_ofFn.mpr hfinj⟩
  have hi' : i < n := by simpa using hi
  rw [List.getElem_ofFn]
  exact List.mem_toFinset.mp (hfmem _)

/-- Level nonemptiness from the marriage condition, through the pure finite-Hall step. -/
private theorem hallLevel_nonempty {Ω : OmegaPart} (H : InternalHallFamily Ω)
    (hmar : H.MarriageCondition) (n : ℕ) : ∃ t, t ∈ hallLevel H.enum n := by
  obtain ⟨t, hlen, hmem, hnd⟩ := exists_hall_tuple (fun k => decodeSeq (H.enum.eval k))
    (fun s => hmar s (fun k => H.enum.eval k) fun k _ => H.enum.pair_eval_mem k) n
  exact ⟨t, (mem_hallLevel H.enum).mpr ⟨hlen, hmem, hnd⟩⟩

/-- **Layer 4: `hallToSystem`.** The Hall family's laws enter only here: `enum_nodup`
supplies fiber duplicate-freeness, the marriage condition supplies nonemptiness through
finite Hall, and truncation of injective tuples supplies `bonding_mem`. No matching is
ever stored in the constructed data. -/
noncomputable def hallToSystem {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (H : InternalHallFamily Ω) (hmar : H.MarriageCondition) : InternalInverseSystem Ω where
  fibers := hallFiberFunction h H.enum
  bonding := treeBondingFunction h
  fiber_nodup := by
    intro n c hc
    rw [hallFiberFunction_mapsTo_iff] at hc
    rw [← hc, decodeSeq_hallFiberCode]
    exact ((hallTuples_nodup _ (hallCandTable_rows_nodup H n) n).map seqCode_injective)
  fiber_nonempty := by
    intro n c hc
    rw [hallFiberFunction_mapsTo_iff] at hc
    rw [← hc, decodeSeq_hallFiberCode]
    obtain ⟨t, ht⟩ := hallLevel_nonempty H hmar n
    exact List.ne_nil_of_mem (List.mem_map_of_mem ht)
  bonding_mem := by
    intro n c c' x y hc hc' hx hy
    rw [hallFiberFunction_mapsTo_iff] at hc hc'
    have hy' := mem_treeBondingGraph_iff.mp hy
    simp only [Nat.unpair_pair] at hy'
    rw [← hc, decodeSeq_hallFiberCode] at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hlen, hmem, hnd⟩ := (mem_hallLevel _).mp ht
    rw [← hc', decodeSeq_hallFiberCode]
    refine List.mem_map.mpr ⟨t.take n, (mem_hallLevel _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.length_take, hlen]
      omega
    · intro i hi
      have hi' : i < n := by simpa [List.length_take, hlen] using hi
      rw [List.getElem_take]
      exact hmem i (by omega)
    · exact hnd.sublist (List.take_sublist n t)
    · rw [hy', decodeSeq_seqCode]

/-! ### The transversal decoder

Reading a section of the compiled system back to a choice function: the level-`(k + 1)`
matching's entry `k`. Takes only the **section** — the type-level fine dependency again —
with `getD` fallback on malformed input. -/

/-- Layer 1 (raw): the value the section selects at index `k`. -/
noncomputable def sectionTransversalValue {Ω : OmegaPart} (s : InternalFunction Ω)
    (k : ℕ) : ℕ :=
  (decodeSeq (s.eval (k + 1))).getD k 0

/-- The graph of the transversal decoder, as a set of `Nat.pair` codes. -/
def sectionTransversalGraph {Ω : OmegaPart} (s : InternalFunction Ω) : Set ℕ :=
  {m | sectionTransversalValue s m.unpair.1 = m.unpair.2}

theorem isGraphOf_sectionTransversalGraph {Ω : OmegaPart} (s : InternalFunction Ω) :
    IsGraphOf (sectionTransversalGraph s) (sectionTransversalValue s) := fun x y => by
  simp [sectionTransversalGraph, Nat.unpair_pair, Set.mem_setOf_eq]

/-- **The decoder's reduction**: the transversal graph is Turing reducible to the section
graph alone — one section lookup per query, then pure computation. -/
theorem sectionTransversalGraph_le_graph {Ω : OmegaPart} (s : InternalFunction Ω) :
    sectionTransversalGraph s ≤ᵀ s.graph.1 := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have heval : Nat.RecursiveIn {charFn s.graph.1} fun k => Part.some (s.eval (k + 1)) :=
    recursiveIn_comp_primrec s.eval_recursiveIn_graph Primrec.succ
  have hval : Nat.RecursiveIn {charFn s.graph.1}
      fun k => Part.some (sectionTransversalValue s k) := by
    have hget : Primrec fun z : ℕ => (decodeSeq z.unpair.1).getD z.unpair.2 0 :=
      Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet hfst hsnd
    exact (recursiveIn_comp_total (recursiveIn_of_primrec hget)
      (recursiveIn_pair_total heval (recursiveIn_of_primrec Primrec.id))).of_eq fun k => by
        simp only [Nat.unpair_pair, id_eq, sectionTransversalValue]
  have hvfst := recursiveIn_comp_primrec hval hfst
  have hpair := recursiveIn_pair_total hvfst (recursiveIn_of_primrec Primrec.id)
  have hpost : Primrec fun z : ℕ => if z.unpair.1 = z.unpair.2.unpair.2 then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hfst (hsnd.comp hsnd)) (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun m => ?_
  simp only [Nat.unpair_pair, id_eq, charFn]
  by_cases hm : sectionTransversalValue s m.unpair.1 = m.unpair.2
  · rw [if_pos hm, if_pos (show m ∈ sectionTransversalGraph s from hm)]
  · rw [if_neg hm, if_neg (show m ∉ sectionTransversalGraph s from hm)]

/-- Layer 3: the decoded transversal as an internal graph-coded function. -/
def sectionTransversalFunction {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (s : InternalFunction Ω) : InternalFunction Ω where
  graph := ⟨sectionTransversalGraph s,
    h.mem_of_reducible s.graph.2 (sectionTransversalGraph_le_graph s)⟩
  total x := ⟨sectionTransversalValue s x,
    (isGraphOf_sectionTransversalGraph s x _).mpr rfl⟩
  singleValued x y y' hy hy' :=
    ((isGraphOf_sectionTransversalGraph s x y).mp hy).symm.trans
      ((isGraphOf_sectionTransversalGraph s x y').mp hy')

/-- The relational surface of the packaged decoder. -/
theorem sectionTransversalFunction_mapsTo_iff {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (s : InternalFunction Ω) {n v : ℕ} :
    (sectionTransversalFunction h s).MapsTo n v ↔ sectionTransversalValue s n = v :=
  isGraphOf_sectionTransversalGraph s n v

/-! ### Layer 4 (correctness): a section decodes to an injective transversal

The port of the ambient argument: section values are nested injective partial
transversals, so entries are stable across levels, distinctness follows from
duplicate-freeness of any covering level, and candidate membership converts to the
relation through the family's checked `mem_iff` — the only place the relation is used. -/

/-- **Correctness of the decoding**: a section of the compiled system decodes to an
injective internal transversal of the family. -/
theorem hallToSystem_section_isTransversal {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (H : InternalHallFamily Ω) (hmar : H.MarriageCondition) {s : InternalFunction Ω}
    (hs : (hallToSystem h H hmar).IsSection s) :
    H.IsTransversal (sectionTransversalFunction h s) := by
  set L : ℕ → List ℕ := fun n => decodeSeq (s.eval n) with hLdef
  have hLmem : ∀ n, L n ∈ hallLevel H.enum n := by
    intro n
    have hfib : (hallToSystem h H hmar).fibers.MapsTo n (hallFiberCode H.enum n) :=
      (isGraphOf_hallFiberGraph H.enum n _).mpr rfl
    have hv := hs.1 n _ _ hfib (s.pair_eval_mem n)
    rw [decodeSeq_hallFiberCode] at hv
    obtain ⟨t, ht, heq⟩ := List.mem_map.mp hv
    have hL : L n = t := by
      change decodeSeq (s.eval n) = t
      rw [← heq, decodeSeq_seqCode]
    rwa [hL]
  have hLlen : ∀ n, (L n).length = n := fun n => ((mem_hallLevel _).mp (hLmem n)).1
  have hLnd : ∀ n, (L n).Nodup := fun n => ((mem_hallLevel _).mp (hLmem n)).2.2
  have hLtake : ∀ n, (L (n + 1)).take n = L n := by
    intro n
    have hbond := hs.2 n _ _ (s.pair_eval_mem (n + 1)) (s.pair_eval_mem n)
    have hb := mem_treeBondingGraph_iff.mp hbond
    simp only [Nat.unpair_pair] at hb
    change (decodeSeq (s.eval (n + 1))).take n = decodeSeq (s.eval n)
    rw [hb, decodeSeq_seqCode]
  have hLprefix : ∀ {n m : ℕ}, n ≤ m → (L m).take n = L n := by
    intro n m hnm
    induction m with
    | zero =>
      obtain rfl : n = 0 := by omega
      exact List.take_of_length_le (by rw [hLlen])
    | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hnm' : n ≤ m := by omega
        rw [← ih hnm', ← hLtake m, List.take_take, Nat.min_eq_left hnm']
      · obtain rfl : n = m + 1 := by omega
        exact List.take_of_length_le (by rw [hLlen])
  have hget : ∀ {n m i : ℕ}, n ≤ m → i < n →
      (L m).getD i 0 = (L n).getD i 0 := by
    intro n m i hnm hi
    have hw : i < ((L m).take n).length := by
      rw [List.length_take, hLlen]
      omega
    have h1 : (L m).getD i 0 = ((L m).take n).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt (by omega)]
    rw [h1, hLprefix hnm]
  constructor
  · intro n y hy
    rw [sectionTransversalFunction_mapsTo_iff] at hy
    have hmem := ((mem_hallLevel _).mp (hLmem (n + 1))).2.1
    have hn : n < (L (n + 1)).length := by rw [hLlen]; omega
    have hyval : y = (L (n + 1))[n] := by
      rw [← hy]
      change (L (n + 1)).getD n 0 = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    refine (H.mem_iff n (H.enum.eval n) y (H.enum.pair_eval_mem n)).mp ?_
    rw [hyval]
    exact hmem n hn
  · intro n n' y hy hy'
    rw [sectionTransversalFunction_mapsTo_iff] at hy hy'
    rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
    · exfalso
      have h1 : (L (n' + 1)).getD n 0 = (L (n + 1)).getD n 0 :=
        hget (by omega) (by omega)
      have h2 : (L (n' + 1)).getD n 0 = (L (n' + 1)).getD n' 0 := by
        rw [h1]
        change sectionTransversalValue s n = sectionTransversalValue s n'
        rw [hy, hy']
      have hn : n < (L (n' + 1)).length := by rw [hLlen]; omega
      have hn' : n' < (L (n' + 1)).length := by rw [hLlen]; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn',
        Option.getD_some, Option.getD_some] at h2
      have := (hLnd (n' + 1)).getElem_inj_iff.mp h2
      omega
    · exact heq
    · exfalso
      have h1 : (L (n + 1)).getD n' 0 = (L (n' + 1)).getD n' 0 :=
        hget (by omega) (by omega)
      have h2 : (L (n + 1)).getD n' 0 = (L (n + 1)).getD n 0 := by
        rw [h1]
        change sectionTransversalValue s n' = sectionTransversalValue s n
        rw [hy, hy']
      have hn : n < (L (n + 1)).length := by rw [hLlen]; omega
      have hn' : n' < (L (n + 1)).length := by rw [hLlen]; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hn', List.getElem?_eq_getElem hn,
        Option.getD_some, Option.getD_some] at h2
      have := (hLnd (n + 1)).getElem_inj_iff.mp h2
      omega

/-! ### The direction theorem -/

/-- **`EFILCω → countable Hall ω`** over a Turing ideal: compile the family to the
internal inverse system of injective partial transversals (`hallToSystem`), take a section,
and decode it to an injective internal transversal (`sectionTransversalFunction`). The
compactness capability is a hypothesis, never derived. -/
theorem countableHallAt_of_efilcAt {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hefilc : EFILCAt Ω) : CountableHallAt Ω := by
  intro H hmar
  obtain ⟨s, hs⟩ := hefilc (hallToSystem h H hmar)
  exact ⟨sectionTransversalFunction h s, hallToSystem_section_isTransversal h H hmar hs⟩

end ReverseMathlib.Omega
