/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.MatchingLocallyFinite
import ReverseMathlib.Omega.KonigFinitelyBranching

/-!
# The reverse route: injection-range existence from locally finite perfect matching
(issue #51)

Hirst's reversal gadget (thesis p. 13, symmetric reading p. 19): from an internal
injection `f`, the marriage problem with edges

* `(2n, 2n)` for every `n`,
* `(2n + 1, 2 f(n))` and `(2 f(n), 2n + 1)` when `f(n) < n`,
* `(2n + 1, 2n + 1)` when `f(n) ≥ n`.

The relation is symmetric, each person knows at most two others (so both
local-finiteness **properties** hold — the neighbor lists are deliberately never
supplied as data: they encode range membership and are not computable from `f`), and
an explicit injective canonical-neighbor choice witnesses the cardinality-form H_sym
on both sides. A perfect matching `g` then decodes the range by the source
observation: `v ∈ ran f` iff girl `2v` is **not** married to boy `2v` or some `m ≤ v`
has `f(m) = v` — one complemented matching query plus one bounded search, so the
decoded range is internal one reduction below the join of the two graphs.

This stage owns the gadget and the decoder and reaches **no jump and no Kőnig
machinery** (gated in `scripts/MetaSmoke.lean`); the tenth fact's reversal is then
the short composition through the seventh fact's checked direction
(`jumpClosedAt_of_injectionRangeExistenceAt`) and the ninth's forward direction
(`finitelyBranchingKonigAt_of_jumpClosedAt`).
-/

namespace ReverseMathlib.Omega

variable {Ω : OmegaPart}

/-! ### The gadget relation -/

/-- Hirst's reversal gadget: the marriage relation an internal injection induces.
Stated relationally through `MapsTo`. -/
def MarriageGadgetAdj (f : InternalFunction Ω) (a b : ℕ) : Prop :=
  (a % 2 = 0 ∧ a = b) ∨
  (∃ n v, f.MapsTo n v ∧ v < n ∧
    ((a = 2 * n + 1 ∧ b = 2 * v) ∨ (a = 2 * v ∧ b = 2 * n + 1))) ∨
  ∃ n v, f.MapsTo n v ∧ n ≤ v ∧ a = 2 * n + 1 ∧ b = 2 * n + 1

/-- The gadget relation is symmetric — the source reason condition H_sym holds. -/
theorem marriageGadgetAdj_symm {f : InternalFunction Ω} {a b : ℕ} (h : MarriageGadgetAdj f a b) :
    MarriageGadgetAdj f b a := by
  rcases h with ⟨he, rfl⟩ | ⟨n, v, hnv, hlt, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
    ⟨n, v, hnv, hle, rfl, rfl⟩
  · exact Or.inl ⟨he, rfl⟩
  · exact Or.inr (Or.inl ⟨n, v, hnv, hlt, Or.inr ⟨rfl, rfl⟩⟩)
  · exact Or.inr (Or.inl ⟨n, v, hnv, hlt, Or.inl ⟨rfl, rfl⟩⟩)
  · exact Or.inr (Or.inr ⟨n, v, hnv, hle, rfl, rfl⟩)

/-- The gadget's edge set, as `Nat.pair` codes. -/
def marriageGadgetEdgeSet (f : InternalFunction Ω) : Set ℕ :=
  {e | MarriageGadgetAdj f e.unpair.1 e.unpair.2}

theorem pair_mem_marriageGadgetEdgeSet {f : InternalFunction Ω} {a b : ℕ} :
    Nat.pair a b ∈ marriageGadgetEdgeSet f ↔ MarriageGadgetAdj f a b := by
  simp [marriageGadgetEdgeSet, Nat.unpair_pair, Set.mem_setOf_eq]

/-- The gadget in evaluation normal form — the shape the two-lookup reduction
decides. Proof-layer adapter only. -/
theorem marriageGadgetAdj_iff_eval {f : InternalFunction Ω} {a b : ℕ} :
    MarriageGadgetAdj f a b ↔
      (a % 2 = 0 ∧ b % 2 = 0 ∧ a = b) ∨
      (a % 2 = 1 ∧ b % 2 = 0 ∧ f.eval (a / 2) = b / 2 ∧ b / 2 < a / 2) ∨
      (a % 2 = 0 ∧ b % 2 = 1 ∧ f.eval (b / 2) = a / 2 ∧ a / 2 < b / 2) ∨
      (a % 2 = 1 ∧ b % 2 = 1 ∧ a = b ∧ a / 2 ≤ f.eval (a / 2)) := by
  constructor
  · rintro (⟨he, rfl⟩ | ⟨n, v, hnv, hlt, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨n, v, hnv, hle, rfl, rfl⟩)
    · exact Or.inl ⟨he, he, rfl⟩
    · refine Or.inr (Or.inl ⟨by omega, by omega, ?_, by omega⟩)
      rw [show (2 * n + 1) / 2 = n from by omega, show 2 * v / 2 = v from by omega]
      exact f.mapsTo_iff_eval_eq.mp hnv
    · refine Or.inr (Or.inr (Or.inl ⟨by omega, by omega, ?_, by omega⟩))
      rw [show (2 * n + 1) / 2 = n from by omega, show 2 * v / 2 = v from by omega]
      exact f.mapsTo_iff_eval_eq.mp hnv
    · refine Or.inr (Or.inr (Or.inr ⟨by omega, by omega, rfl, ?_⟩))
      rw [show (2 * n + 1) / 2 = n from by omega]
      have := f.mapsTo_iff_eval_eq.mp hnv
      omega
  · rintro (⟨ha, -, rfl⟩ | ⟨ha, hb, hev, hlt⟩ | ⟨ha, hb, hev, hlt⟩ |
      ⟨ha, hb, rfl, hle⟩)
    · exact Or.inl ⟨ha, rfl⟩
    · refine Or.inr (Or.inl ⟨a / 2, b / 2, f.mapsTo_iff_eval_eq.mpr hev, hlt,
        Or.inl ⟨by omega, by omega⟩⟩)
    · exact Or.inr (Or.inl ⟨b / 2, a / 2, f.mapsTo_iff_eval_eq.mpr hev, hlt,
        Or.inr ⟨by omega, by omega⟩⟩)
    · exact Or.inr (Or.inr ⟨a / 2, f.eval (a / 2),
        f.mapsTo_iff_eval_eq.mpr rfl, hle, by omega, by omega⟩)

/-! ### Local finiteness — as properties -/

/-- Every boy knows boundedly many girls: an odd boy's girls sit below him, and an
even boy's second girl (if any) is the unique odd witness of his half — uniqueness
through the injectivity of `f`. The bound is an existential property; the reversal
never supplies neighbor data. -/
theorem marriageGadget_left_locally_finite (f : InternalFunction Ω) (hf : f.IsInjective)
    (a : ℕ) : ∃ k, ∀ b, Nat.pair a b ∈ marriageGadgetEdgeSet f → b < k := by
  classical
  by_cases hm : ∃ m, f.MapsTo m (a / 2) ∧ a / 2 < m
  · refine ⟨max a (2 * hm.choose + 1) + 1, fun b hb => ?_⟩
    rcases pair_mem_marriageGadgetEdgeSet.mp hb with ⟨-, hab⟩ |
      ⟨n, v, hnv, hlt, ⟨ha, hbv⟩ | ⟨ha, hbv⟩⟩ | ⟨n, v, hnv, hle, ha, hbv⟩
    · omega
    · omega
    · have hveq : v = a / 2 := by omega
      have := hf n hm.choose (a / 2) (hveq ▸ hnv) hm.choose_spec.1
      omega
    · omega
  · refine ⟨a + 1, fun b hb => ?_⟩
    rcases pair_mem_marriageGadgetEdgeSet.mp hb with ⟨-, hab⟩ |
      ⟨n, v, hnv, hlt, ⟨ha, hbv⟩ | ⟨ha, hbv⟩⟩ | ⟨n, v, hnv, hle, ha, hbv⟩
    · omega
    · omega
    · exact absurd ⟨n, by rwa [show v = a / 2 from by omega] at hnv, by omega⟩ hm
    · omega

/-- The girls' side, through symmetry. -/
theorem marriageGadget_right_locally_finite (f : InternalFunction Ω) (hf : f.IsInjective)
    (b : ℕ) : ∃ k, ∀ a, Nat.pair a b ∈ marriageGadgetEdgeSet f → a < k := by
  obtain ⟨k, hk⟩ := marriageGadget_left_locally_finite f hf b
  exact ⟨k, fun a ha => hk a (pair_mem_marriageGadgetEdgeSet.mpr
    (marriageGadgetAdj_symm (pair_mem_marriageGadgetEdgeSet.mp ha)))⟩

/-! ### The symmetric marriage condition -/

open Classical in
/-- The canonical neighbor of person `a` in the gadget: an odd person takes their
injection value's girl when it sits below them and themselves otherwise; an even
person takes the unique odd witness of their half if one exists and themselves
otherwise. Injective, which is exactly the cardinality-form H_sym. -/
noncomputable def marriageGadgetPick (f : InternalFunction Ω) (a : ℕ) : ℕ :=
  if a % 2 = 1 then
    if f.eval (a / 2) < a / 2 then 2 * f.eval (a / 2) else a
  else
    if h : ∃ m, f.MapsTo m (a / 2) ∧ a / 2 < m then 2 * h.choose + 1 else a

/-- The canonical neighbor is a neighbor. -/
theorem marriageGadgetAdj_pick (f : InternalFunction Ω) (a : ℕ) :
    MarriageGadgetAdj f a (marriageGadgetPick f a) := by
  classical
  rw [marriageGadgetPick]
  by_cases hpar : a % 2 = 1
  · rw [if_pos hpar]
    by_cases hlt : f.eval (a / 2) < a / 2
    · rw [if_pos hlt]
      exact Or.inr (Or.inl ⟨a / 2, f.eval (a / 2), f.mapsTo_iff_eval_eq.mpr rfl,
        hlt, Or.inl ⟨by omega, rfl⟩⟩)
    · rw [if_neg hlt]
      exact Or.inr (Or.inr ⟨a / 2, f.eval (a / 2), f.mapsTo_iff_eval_eq.mpr rfl,
        by omega, by omega, by omega⟩)
  · rw [if_neg hpar]
    by_cases hm : ∃ m, f.MapsTo m (a / 2) ∧ a / 2 < m
    · rw [dif_pos hm]
      exact Or.inr (Or.inl ⟨hm.choose, a / 2, hm.choose_spec.1, hm.choose_spec.2,
        Or.inr ⟨by omega, rfl⟩⟩)
    · rw [dif_neg hm]
      exact Or.inl ⟨by omega, rfl⟩

/-- **The canonical neighbor choice is injective** — the finite marriage condition
in one function: distinct people take distinct canonical neighbors, by the
injectivity and single-valuedness of `f` and a parity analysis of the four
branches. -/
theorem marriageGadgetPick_injective (f : InternalFunction Ω) (hf : f.IsInjective) :
    Function.Injective (marriageGadgetPick f) := by
  classical
  have heinj : ∀ {x y : ℕ}, f.eval x = f.eval y → x = y := fun {x y} h =>
    hf x y (f.eval y) (h ▸ f.mapsTo_iff_eval_eq.mpr rfl) (f.mapsTo_iff_eval_eq.mpr rfl)
  intro a a' hpick
  rw [marriageGadgetPick, marriageGadgetPick] at hpick
  by_cases hpar : a % 2 = 1 <;> by_cases hpar' : a' % 2 = 1
  · rw [if_pos hpar, if_pos hpar'] at hpick
    by_cases hlt : f.eval (a / 2) < a / 2 <;>
      by_cases hlt' : f.eval (a' / 2) < a' / 2
    · rw [if_pos hlt, if_pos hlt'] at hpick
      have := heinj (show f.eval (a / 2) = f.eval (a' / 2) by omega)
      omega
    · rw [if_pos hlt, if_neg hlt'] at hpick
      omega
    · rw [if_neg hlt, if_pos hlt'] at hpick
      omega
    · rw [if_neg hlt, if_neg hlt'] at hpick
      exact hpick
  · rw [if_pos hpar, if_neg hpar'] at hpick
    by_cases hlt : f.eval (a / 2) < a / 2
    · rw [if_pos hlt] at hpick
      by_cases hm : ∃ m, f.MapsTo m (a' / 2) ∧ a' / 2 < m
      · rw [dif_pos hm] at hpick
        omega
      · rw [dif_neg hm] at hpick
        exact absurd ⟨a / 2, f.mapsTo_iff_eval_eq.mpr (show f.eval (a / 2) = a' / 2
          by omega), by omega⟩ hm
    · rw [if_neg hlt] at hpick
      by_cases hm : ∃ m, f.MapsTo m (a' / 2) ∧ a' / 2 < m
      · rw [dif_pos hm] at hpick
        have hn : hm.choose = a / 2 := by omega
        have := f.mapsTo_iff_eval_eq.mp (hn ▸ hm.choose_spec.1)
        have := hm.choose_spec.2
        omega
      · rw [dif_neg hm] at hpick
        omega
  · rw [if_neg hpar, if_pos hpar'] at hpick
    by_cases hlt' : f.eval (a' / 2) < a' / 2
    · rw [if_pos hlt'] at hpick
      by_cases hm : ∃ m, f.MapsTo m (a / 2) ∧ a / 2 < m
      · rw [dif_pos hm] at hpick
        omega
      · rw [dif_neg hm] at hpick
        exact absurd ⟨a' / 2, f.mapsTo_iff_eval_eq.mpr (show f.eval (a' / 2) = a / 2
          by omega), by omega⟩ hm
    · rw [if_neg hlt'] at hpick
      by_cases hm : ∃ m, f.MapsTo m (a / 2) ∧ a / 2 < m
      · rw [dif_pos hm] at hpick
        have hn : hm.choose = a' / 2 := by omega
        have := f.mapsTo_iff_eval_eq.mp (hn ▸ hm.choose_spec.1)
        have := hm.choose_spec.2
        omega
      · rw [dif_neg hm] at hpick
        omega
  · rw [if_neg hpar, if_neg hpar'] at hpick
    by_cases hm : ∃ m, f.MapsTo m (a / 2) ∧ a / 2 < m <;>
      by_cases hm' : ∃ m, f.MapsTo m (a' / 2) ∧ a' / 2 < m
    · rw [dif_pos hm, dif_pos hm'] at hpick
      have hmeq : hm.choose = hm'.choose := by omega
      have hv := f.singleValued hm.choose (a / 2) (a' / 2) hm.choose_spec.1
        (hmeq ▸ hm'.choose_spec.1)
      omega
    · rw [dif_pos hm, dif_neg hm'] at hpick
      omega
    · rw [dif_neg hm, dif_pos hm'] at hpick
      omega
    · rw [dif_neg hm, dif_neg hm'] at hpick
      exact hpick

/-! ### Internality of the gadget -/

/-- **The gadget's edge set is one reduction below the injection's graph**: two
unique-graph lookups (at each endpoint's half) and a pure parity decision. -/
theorem marriageGadgetEdgeSet_le_graph (f : InternalFunction Ω) :
    marriageGadgetEdgeSet f ≤ᵀ f.graph.1 := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hv1 : Nat.RecursiveIn {charFn f.graph.1}
      fun e => Part.some (f.eval (e.unpair.1 / 2)) :=
    recursiveIn_comp_primrec f.eval_recursiveIn_graph
      (Primrec.nat_div.comp hfst (Primrec.const 2))
  have hv2 : Nat.RecursiveIn {charFn f.graph.1}
      fun e => Part.some (f.eval (e.unpair.2 / 2)) :=
    recursiveIn_comp_primrec f.eval_recursiveIn_graph
      (Primrec.nat_div.comp hsnd (Primrec.const 2))
  have hpack := recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id)
    (recursiveIn_pair_total hv1 hv2)
  have hpost : Primrec fun z : ℕ =>
      if (z.unpair.1.unpair.1 % 2 = 0 ∧ z.unpair.1.unpair.2 % 2 = 0 ∧
            z.unpair.1.unpair.1 = z.unpair.1.unpair.2) ∨
          (z.unpair.1.unpair.1 % 2 = 1 ∧ z.unpair.1.unpair.2 % 2 = 0 ∧
            z.unpair.2.unpair.1 = z.unpair.1.unpair.2 / 2 ∧
            z.unpair.1.unpair.2 / 2 < z.unpair.1.unpair.1 / 2) ∨
          (z.unpair.1.unpair.1 % 2 = 0 ∧ z.unpair.1.unpair.2 % 2 = 1 ∧
            z.unpair.2.unpair.2 = z.unpair.1.unpair.1 / 2 ∧
            z.unpair.1.unpair.1 / 2 < z.unpair.1.unpair.2 / 2) ∨
          (z.unpair.1.unpair.1 % 2 = 1 ∧ z.unpair.1.unpair.2 % 2 = 1 ∧
            z.unpair.1.unpair.1 = z.unpair.1.unpair.2 ∧
            z.unpair.1.unpair.1 / 2 ≤ z.unpair.2.unpair.1)
      then 1 else 0 := by
    have ha : Primrec fun z : ℕ => z.unpair.1.unpair.1 := hfst.comp hfst
    have hb : Primrec fun z : ℕ => z.unpair.1.unpair.2 := hsnd.comp hfst
    have hp1 : Primrec fun z : ℕ => z.unpair.2.unpair.1 := hfst.comp hsnd
    have hp2 : Primrec fun z : ℕ => z.unpair.2.unpair.2 := hsnd.comp hsnd
    have hamod : Primrec fun z : ℕ => z.unpair.1.unpair.1 % 2 :=
      Primrec.nat_mod.comp ha (Primrec.const 2)
    have hbmod : Primrec fun z : ℕ => z.unpair.1.unpair.2 % 2 :=
      Primrec.nat_mod.comp hb (Primrec.const 2)
    have hadiv : Primrec fun z : ℕ => z.unpair.1.unpair.1 / 2 :=
      Primrec.nat_div.comp ha (Primrec.const 2)
    have hbdiv : Primrec fun z : ℕ => z.unpair.1.unpair.2 / 2 :=
      Primrec.nat_div.comp hb (Primrec.const 2)
    exact Primrec.ite (PrimrecPred.or
        (PrimrecPred.and (Primrec.eq.comp hamod (Primrec.const 0))
          (PrimrecPred.and (Primrec.eq.comp hbmod (Primrec.const 0))
            (Primrec.eq.comp ha hb)))
        (PrimrecPred.or
          (PrimrecPred.and (Primrec.eq.comp hamod (Primrec.const 1))
            (PrimrecPred.and (Primrec.eq.comp hbmod (Primrec.const 0))
              (PrimrecPred.and (Primrec.eq.comp hp1 hbdiv)
                (Primrec.nat_lt.comp hbdiv hadiv))))
          (PrimrecPred.or
            (PrimrecPred.and (Primrec.eq.comp hamod (Primrec.const 0))
              (PrimrecPred.and (Primrec.eq.comp hbmod (Primrec.const 1))
                (PrimrecPred.and (Primrec.eq.comp hp2 hadiv)
                  (Primrec.nat_lt.comp hadiv hbdiv))))
            (PrimrecPred.and (Primrec.eq.comp hamod (Primrec.const 1))
              (PrimrecPred.and (Primrec.eq.comp hbmod (Primrec.const 1))
                (PrimrecPred.and (Primrec.eq.comp ha hb)
                  (Primrec.nat_le.comp hadiv hp1)))))))
      (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpack).of_eq fun e => ?_
  simp only [Nat.unpair_pair, id_eq, charFn]
  have hsem : ((e.unpair.1 % 2 = 0 ∧ e.unpair.2 % 2 = 0 ∧ e.unpair.1 = e.unpair.2) ∨
      (e.unpair.1 % 2 = 1 ∧ e.unpair.2 % 2 = 0 ∧
        f.eval (e.unpair.1 / 2) = e.unpair.2 / 2 ∧
        e.unpair.2 / 2 < e.unpair.1 / 2) ∨
      (e.unpair.1 % 2 = 0 ∧ e.unpair.2 % 2 = 1 ∧
        f.eval (e.unpair.2 / 2) = e.unpair.1 / 2 ∧
        e.unpair.1 / 2 < e.unpair.2 / 2) ∨
      (e.unpair.1 % 2 = 1 ∧ e.unpair.2 % 2 = 1 ∧ e.unpair.1 = e.unpair.2 ∧
        e.unpair.1 / 2 ≤ f.eval (e.unpair.1 / 2))) ↔
      e ∈ marriageGadgetEdgeSet f :=
    (marriageGadgetAdj_iff_eval (f := f) (a := e.unpair.1) (b := e.unpair.2)).symm
  by_cases he : e ∈ marriageGadgetEdgeSet f
  · rw [if_pos (hsem.mpr he), if_pos he]
  · rw [if_neg (fun hyes => he (hsem.mp hyes)), if_neg he]

/-- The gadget, packaged as an internal locally finite marriage problem — edges one
reduction below the injection's graph, both local-finiteness properties, no supplied
neighbor data anywhere. -/
def marriageGadgetBigraph (hΩ : IsTuringIdeal Ω) (f : InternalFunction Ω)
    (hf : f.IsInjective) : InternalLocallyFiniteBigraph Ω where
  edges := ⟨marriageGadgetEdgeSet f,
    hΩ.mem_of_reducible f.graph.2 (marriageGadgetEdgeSet_le_graph f)⟩
  left_locally_finite := marriageGadget_left_locally_finite f hf
  right_locally_finite := marriageGadget_right_locally_finite f hf

/-- **The gadget satisfies the cardinality-form H_sym** on both sides: the injective
canonical-neighbor choice maps any duplicate-free list to a duplicate-free witness
list of the same length, and symmetry serves the girls' side. -/
theorem marriageGadgetBigraph_satisfiesSymmetricHall (hΩ : IsTuringIdeal Ω)
    (f : InternalFunction Ω) (hf : f.IsInjective) :
    (marriageGadgetBigraph hΩ f hf).SatisfiesSymmetricHall := by
  constructor
  · intro l hl
    refine ⟨l.map (marriageGadgetPick f), hl.map (marriageGadgetPick_injective f hf),
      le_of_eq (l.length_map _).symm, ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ⟨a, ha, pair_mem_marriageGadgetEdgeSet.mpr (marriageGadgetAdj_pick f a)⟩
  · intro l hl
    refine ⟨l.map (marriageGadgetPick f), hl.map (marriageGadgetPick_injective f hf),
      le_of_eq (l.length_map _).symm, ?_⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ⟨b, hb, pair_mem_marriageGadgetEdgeSet.mpr
      (marriageGadgetAdj_symm (marriageGadgetAdj_pick f b))⟩

/-! ### The range decoder -/

/-- The decoded range: `v` is a value of `f` exactly when girl `2v` is not married
to boy `2v` or some witness at most `v` maps to `v` — the source decoding, stated
relationally. -/
def marriageGadgetRangeSet (g f : InternalFunction Ω) : Set ℕ :=
  {v | ¬ g.MapsTo (2 * v) (2 * v) ∨ ∃ m ≤ v, f.MapsTo m v}

/-- **The decoder's reduction**: one complemented matching query plus one bounded
transcript of injection bits — the decoded range is one reduction below the join of
the matching's and the injection's graphs. -/
theorem marriageGadgetRangeSet_le_join (g f : InternalFunction Ω) :
    marriageGadgetRangeSet g f ≤ᵀ joinSet g.graph.1 f.graph.1 := by
  classical
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  -- the complemented matching bit at (2v, 2v), through the left of the join
  have hGb : Nat.RecursiveIn {charFn g.graph.1} fun x => Part.some
      (charFnTot g.graph.1 x) := by
    refine (Nat.RecursiveIn.oracle (O := {charFn g.graph.1})
      (charFn g.graph.1) rfl).of_eq fun x => ?_
    rw [charFn_eq_coe]
    rfl
  have hgq : Primrec fun v : ℕ => Nat.pair (2 * v) (2 * v) := by
    have hdouble : Primrec fun v : ℕ => 2 * v :=
      Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
    exact Primrec₂.comp (f := Nat.pair) Primrec₂.natPair hdouble hdouble
  have hgbit : Nat.RecursiveIn {charFn (joinSet g.graph.1 f.graph.1)} fun v =>
      Part.some (charFnTot g.graph.1 (Nat.pair (2 * v) (2 * v))) :=
    recursiveIn_of_turingReducible (recursiveIn_comp_primrec hGb hgq)
      (left_le_joinSet _ _)
  -- the bounded injection transcript, through the right of the join
  have hFb : Nat.RecursiveIn {charFn f.graph.1} fun x => Part.some
      (charFnTot f.graph.1 x) := by
    refine (Nat.RecursiveIn.oracle (O := {charFn f.graph.1})
      (charFn f.graph.1) rfl).of_eq fun x => ?_
    rw [charFn_eq_coe]
    rfl
  have hfq : Primrec fun z : ℕ => Nat.pair z.unpair.2 z.unpair.1 :=
    Primrec₂.comp (f := Nat.pair) Primrec₂.natPair hsnd hfst
  have htab := valueTable_recursiveIn_param
    (f := fun v m => charFnTot f.graph.1 (Nat.pair m v))
    (recursiveIn_comp_primrec hFb hfq)
  have htabj : Nat.RecursiveIn {charFn (joinSet g.graph.1 f.graph.1)} fun p =>
      Part.some (valueTable (fun m => charFnTot f.graph.1 (Nat.pair m p.unpair.1))
        p.unpair.2) :=
    recursiveIn_of_turingReducible htab (right_le_joinSet _ _)
  have hcl : Nat.RecursiveIn {charFn (joinSet g.graph.1 f.graph.1)} fun v =>
      Part.some (Nat.pair (id v) (v + 1)) :=
    recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id)
      (recursiveIn_of_primrec Primrec.succ)
  have htabv : Nat.RecursiveIn {charFn (joinSet g.graph.1 f.graph.1)} fun v =>
      Part.some (valueTable (fun m => charFnTot f.graph.1 (Nat.pair m v)) (v + 1)) :=
    (recursiveIn_comp_total htabj hcl).of_eq fun v => by simp only [Nat.unpair_pair, id_eq]
  -- package (gbit, table) and decide purely
  have hpack := recursiveIn_pair_total hgbit htabv
  have hpost : Primrec fun z : ℕ =>
      if z.unpair.1 ≠ 1 ∨
          (decodeSeq z.unpair.2).findIdx (· == 1) ≠ (decodeSeq z.unpair.2).length
      then 1 else 0 := by
    have htb : Primrec fun z : ℕ => decodeSeq z.unpair.2 := primrec_decodeSeq.comp hsnd
    exact Primrec.ite (PrimrecPred.or
        (PrimrecPred.not (Primrec.eq.comp hfst (Primrec.const 1)))
        (PrimrecPred.not (Primrec.eq.comp
          (Primrec.list_findIdx htb
            (Primrec.beq.comp Primrec.snd (Primrec.const 1)))
          (Primrec.list_length.comp htb))))
      (Primrec.const 1) (Primrec.const 0)
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpack).of_eq fun v => ?_
  simp only [Nat.unpair_pair, decodeSeq_valueTable, charFn]
  have hone : ∀ (A : Set ℕ) (x : ℕ), charFnTot A x = 1 ↔ x ∈ A := by
    intro A x
    by_cases h : x ∈ A <;> simp [charFnTot, h]
  have hfind : ((List.range (v + 1)).map fun m =>
      charFnTot f.graph.1 (Nat.pair m v)).findIdx (· == 1) ≠
        ((List.range (v + 1)).map fun m =>
          charFnTot f.graph.1 (Nat.pair m v)).length ↔
      ∃ m ≤ v, f.MapsTo m v := by
    constructor
    · intro hne
      by_contra hno
      refine hne (List.findIdx_eq_length.mpr ?_)
      intro x hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      have hnm : ¬ f.MapsTo m v := fun hmap =>
        hno ⟨m, Nat.lt_succ_iff.mp (List.mem_range.mp hm), hmap⟩
      exact beq_eq_false_iff_ne.mpr fun hbeq => hnm ((hone _ _).mp hbeq)
    · rintro ⟨m, hm, hmv⟩ hEq
      have hall := List.findIdx_eq_length.mp hEq
      have hmem : charFnTot f.graph.1 (Nat.pair m v) ∈
          (List.range (v + 1)).map fun m => charFnTot f.graph.1 (Nat.pair m v) :=
        List.mem_map.mpr ⟨m, List.mem_range.mpr (by omega), rfl⟩
      have hzero := hall _ hmem
      rw [(hone _ _).mpr hmv] at hzero
      simp at hzero
  by_cases hv : v ∈ marriageGadgetRangeSet g f
  · rw [if_pos ?_, if_pos hv]
    rcases hv with hng | hex
    · exact Or.inl (fun h1 => hng ((hone _ _).mp h1))
    · exact Or.inr (hfind.mpr hex)
  · rw [if_neg ?_, if_neg hv]
    rintro (h1 | hex)
    · exact hv (Or.inl fun hmap => h1 ((hone _ _).mpr hmap))
    · exact hv (Or.inr (hfind.mp hex))

/-! ### The two named reverse theorems -/

/-- **Locally finite perfect matching gives injection-range existence** over the
Turing-ideal closure conditions — the intermediate reverse stage, owning the gadget
and the range decoder. Proof architecture for the tenth fact's reversal;
deliberately not a registered fact of its own, and reaching no jump and no Kőnig
machinery. -/
theorem injectionRangeExistenceAt_of_locallyFinitePerfectMatchingAt {Ω : OmegaPart}
    (hΩ : IsTuringIdeal Ω) (hM : LocallyFinitePerfectMatchingAt Ω) :
    InjectionRangeExistenceAt Ω := by
  intro f hf
  obtain ⟨g, hgE, hgInj, hgSurj⟩ :=
    hM (marriageGadgetBigraph hΩ f hf) (marriageGadgetBigraph_satisfiesSymmetricHall hΩ f hf)
  refine ⟨⟨marriageGadgetRangeSet g f,
    hΩ.mem_of_reducible (hΩ.join g.graph.2 f.graph.2) (marriageGadgetRangeSet_le_join g f)⟩, ?_⟩
  intro v
  constructor
  · rintro (hng | ⟨m, -, hmv⟩)
    · -- girl `2v` married elsewhere: her husband can only be an odd witness
      obtain ⟨a, ha⟩ := hgSurj (2 * v)
      have hadj : MarriageGadgetAdj f a (2 * v) :=
        pair_mem_marriageGadgetEdgeSet.mp (hgE a (2 * v) ha)
      rcases hadj with ⟨-, hab⟩ | ⟨n, v', hnv, hlt, ⟨ha', hbv⟩ | ⟨ha', hbv⟩⟩ |
        ⟨n, v', hnv, hle, ha', hbv⟩
      · exact absurd (hab ▸ ha) hng
      · exact ⟨n, by rwa [show v' = v from by omega] at hnv⟩
      · omega
      · omega
    · exact ⟨m, hmv⟩
  · rintro ⟨m, hmv⟩
    by_cases hmle : m ≤ v
    · exact Or.inr ⟨m, hmle, hmv⟩
    · -- a late witness: boy `2m + 1` claims girl `2v`, so the diagonal is broken
      left
      intro hg2v
      obtain ⟨w, hw⟩ := g.total (2 * m + 1)
      have hadj : MarriageGadgetAdj f (2 * m + 1) w :=
        pair_mem_marriageGadgetEdgeSet.mp (hgE _ _ hw)
      rcases hadj with ⟨ha, -⟩ | ⟨n, v', hnv, hlt, ⟨ha', hbv⟩ | ⟨ha', hbv⟩⟩ |
        ⟨n, v', hnv, hle, ha', hbv⟩
      · omega
      · -- his wife is `2 f(m) = 2v`: two husbands for girl `2v`
        have hn : n = m := by omega
        have hv' : v' = v := f.singleValued m v' v (hn ▸ hnv) hmv
        have := hgInj (2 * m + 1) (2 * v) (2 * v)
          (by rwa [hbv, hv'] at hw) hg2v
        omega
      · omega
      · -- the self-loop clause would put the witness at or below `v`
        have hn : n = m := by omega
        have := f.singleValued m v' v (hn ▸ hnv) hmv
        omega

/-- **Full finitely-branching Kőnig from locally finite perfect matching**: the
tenth fact's reversal — the gadget stage into injection-range existence, then the
seventh fact's checked direction into jump closure, then the ninth's forward
direction. -/
theorem finitelyBranchingKonigAt_of_locallyFinitePerfectMatchingAt {Ω : OmegaPart}
    (hΩ : IsTuringIdeal Ω) (hM : LocallyFinitePerfectMatchingAt Ω) :
    FinitelyBranchingKonigAt Ω :=
  finitelyBranchingKonigAt_of_jumpClosedAt hΩ
    (jumpClosedAt_of_injectionRangeExistenceAt hΩ
      (injectionRangeExistenceAt_of_locallyFinitePerfectMatchingAt hΩ hM))

end ReverseMathlib.Omega
