/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.SeparationGadgetReduction

/-!
# The four-query separator (issue #42, slice 4b)

The decoder of the reversal: the separating set read off a perfect matching of
the gadget, following Shafer's `Z` (text p. 158) — `n` is in the set exactly
when the matching pairs `xₙ` with `y⁰ₙ,₀` and `x²ₙ,₀` with `yₙ` (or the mirror
`y¹`/`x³` pattern). The raw definition and its reduction mention **only the
matching graph**, as a bare set: four explicit membership queries and a boolean
combination — neither input injection, nor the gadget structure, nor any
adjacency machinery appears (fine-dependency gate in `scripts/MetaSmoke.lean`).
The injections, their injectivity and disjointness, and perfect-matching
correctness enter only in the forced-chain proof of `SeparatesRanges`.
-/

namespace ReverseMathlib.Omega

namespace SeparationGadget

/-- Layer 1 (raw, the specification): the separating set of a matching graph —
four explicit membership queries per `n`, mentioning **only** the graph `M`. -/
def separatorSet (M : Set ℕ) : Set ℕ :=
  {n | (Nat.pair (xPlain n) (ySpec 0 n) ∈ M ∧
      Nat.pair (xChain 2 n 0) (yPlain n) ∈ M) ∨
    (Nat.pair (xPlain n) (ySpec 1 n) ∈ M ∧
      Nat.pair (xChain 3 n 0) (yPlain n) ∈ M)}

/-- **Layer 2**: the separator is Turing-reducible to the matching graph —
four queries and a boolean combination. -/
theorem separatorSet_le_graph (M : Set ℕ) : separatorSet M ≤ᵀ M := by
  classical
  have hqs : ∀ e : ℕ → ℕ, Primrec e →
      Nat.RecursiveIn {charFn M} fun n => charFn M (e n) := fun e he =>
    recursiveIn_comp_partrec (Nat.RecursiveIn.oracle (O := {charFn M}) _ rfl)
      ((Nat.Partrec.of_primrec (Primrec.nat_iff.mp he)).of_eq fun _ => rfl)
  have hpS : ∀ b : ℕ, Primrec fun n => Nat.pair (xPlain n) (ySpec b n) := fun b =>
    Primrec₂.natPair.comp primrec_xPlain
      (primrec_ySpecT.comp (Primrec.pair (.const b) Primrec.id))
  have hpC : ∀ j : ℕ, Primrec fun n => Nat.pair (xChain j n 0) (yPlain n) := fun j =>
    Primrec₂.natPair.comp
      (primrec_xChainT.comp (Primrec.pair (.const j)
        (Primrec.pair Primrec.id (.const 0))))
      primrec_yPlain
  have h1 := hqs _ (hpS 0)
  have h2 := hqs _ (hpC 2)
  have h3 := hqs _ (hpS 1)
  have h4 := hqs _ (hpC 3)
  have hp := (h1.pair h2).pair (h3.pair h4)
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1.unpair.1 = 1 ∧ m.unpair.1.unpair.2 = 1 then 1
        else if m.unpair.2.unpair.1 = 1 ∧ m.unpair.2.unpair.2 = 1 then 1
        else 0) := by
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1.unpair.1 = 1 ∧ m.unpair.1.unpair.2 = 1 then 1
          else if m.unpair.2.unpair.1 = 1 ∧ m.unpair.2.unpair.2 = 1 then 1
          else 0 :=
      Primrec.ite
        ((PrimrecPred.and
          (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp
            (Primrec.fst.comp Primrec.unpair))) (.const 1))
          (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.fst.comp Primrec.unpair))) (.const 1))))
        (.const 1)
        (Primrec.ite
          ((PrimrecPred.and
            (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp
              (Primrec.snd.comp Primrec.unpair))) (.const 1))
            (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp
              (Primrec.snd.comp Primrec.unpair))) (.const 1))))
          (.const 1) (.const 0))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hp).of_eq fun n => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases hA : Nat.pair (xPlain n) (ySpec 0 n) ∈ M <;>
    by_cases hB : Nat.pair (xChain 2 n 0) (yPlain n) ∈ M <;>
    by_cases hC : Nat.pair (xPlain n) (ySpec 1 n) ∈ M <;>
    by_cases hD : Nat.pair (xChain 3 n 0) (yPlain n) ∈ M <;>
    simp [separatorSet, hA, hB, hC, hD]

end SeparationGadget

open SeparationGadget in
/-- Layer 3: the separator as an internal set — ideal closure on the layer-2
reducibility. Mentions only the matching function's graph. -/
def gadgetSeparator {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (M : InternalFunction Ω) : Ω.InternalSet :=
  ⟨separatorSet M.graph.1, h.mem_of_reducible M.graph.2 (separatorSet_le_graph _)⟩

namespace SeparationGadget

/-! ### The generic degree-two matching lemmas

These consume only the perfect-matching structure — the injections' properties
stay out until the chain proof itself. -/

section ForcedChains

variable {Ω : OmegaPart} {h : IsTuringIdeal Ω} {f g M : InternalFunction Ω}

private theorem mem_pair'' {a x y : ℕ} : a ∈ [x, y] ↔ a = x ∨ a = y := by
  simp

/-- A matched left vertex selects one of its two enumerated neighbors. -/
theorem matched_left (hM : (gadgetBigraph h f g).IsPerfectMatching M) (v : ℕ) :
    ∃ w, M.MapsTo v w ∧ w ∈ leftRow f.graph.1 g.graph.1 v := by
  obtain ⟨w, hw⟩ := M.total v
  exact ⟨w, hw, mem_gadgetEdges_row.mp (hM.1 v w hw)⟩

/-- **The forcing lemma**: once a left vertex's second listed neighbor is
occupied by a different left vertex, injectivity forces the first. -/
theorem forced_left_snd (hM : (gadgetBigraph h f g).IsPerfectMatching M)
    {v v' w1 w2 : ℕ} (hrow : leftRow f.graph.1 g.graph.1 v = [w1, w2])
    (hocc : M.MapsTo v' w2) (hne : v' ≠ v) : M.MapsTo v w1 := by
  obtain ⟨w, hw, hwrow⟩ := matched_left hM v
  rw [hrow] at hwrow
  rcases mem_pair''.mp hwrow with rfl | rfl
  · exact hw
  · exact absurd (hM.2.1 v' v w hocc hw) hne

/-- The mirror forcing: first neighbor occupied elsewhere forces the second. -/
theorem forced_left_fst (hM : (gadgetBigraph h f g).IsPerfectMatching M)
    {v v' w1 w2 : ℕ} (hrow : leftRow f.graph.1 g.graph.1 v = [w1, w2])
    (hocc : M.MapsTo v' w1) (hne : v' ≠ v) : M.MapsTo v w2 := by
  obtain ⟨w, hw, hwrow⟩ := matched_left hM v
  rw [hrow] at hwrow
  rcases mem_pair''.mp hwrow with rfl | rfl
  · exact absurd (hM.2.1 v' v w hocc hw) hne
  · exact hw

/-! ### Classifier values under the correctness hypotheses -/

/-- With `f` hitting `n` exactly at `m` and disjoint ranges, the classifier at
`(n, i)` is `0` at `i = m` and `2` elsewhere. -/
theorem class_of_f (hfi : f.IsInjective) (hdisj : DisjointRanges f g)
    {m n : ℕ} (hm : f.MapsTo m n) (i : ℕ) :
    hitClass f.graph.1 g.graph.1 n i = if i = m then 0 else 2 := by
  by_cases him : i = m
  · subst him
    rw [if_pos rfl]
    exact hitClass_eq_zero_iff.mpr hm
  · rw [if_neg him]
    exact hitClass_eq_two_iff.mpr
      ⟨fun hF => him (hfi i m n hF hm), fun hG => hdisj m i n hm hG⟩

/-- With `g` hitting `n` exactly at `m` and disjoint ranges, the classifier at
`(n, i)` is `1` at `i = m` and `2` elsewhere. -/
theorem class_of_g (hgi : g.IsInjective) (hdisj : DisjointRanges f g)
    {m n : ℕ} (hm : g.MapsTo m n) (i : ℕ) :
    hitClass f.graph.1 g.graph.1 n i = if i = m then 1 else 2 := by
  by_cases him : i = m
  · subst him
    rw [if_pos rfl]
    exact hitClass_eq_one_iff.mpr ⟨hm, fun hF => hdisj i i n hF hm⟩
  · rw [if_neg him]
    exact hitClass_eq_two_iff.mpr
      ⟨fun hF => hdisj i m n hF hm, fun hG => him (hgi i m n hG hm)⟩

/-! ### The three chain lemmas

All parameterized by the class profile (`2` away from `m`), so the `f` and `g`
cases become short truth-table arguments at the end. -/

/-- Row shape for a spec-lane chain vertex away from the hit index. -/
private theorem lane_row {b n i : ℕ} (hb : b < 2)
    (hcls : hitClass f.graph.1 g.graph.1 n i = 2) :
    leftRow f.graph.1 g.graph.1 (xChain b n i) = [yChain b n i, yAt b n i] := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;>
    rw [leftRow_xChain _ _ _ n i (by omega)] <;>
    simp [hcls]

/-- Row shape for a descending-lane chain vertex away from the hit index. -/
private theorem desc_row {j2 n i : ℕ} (hj2 : j2 = 2 ∨ j2 = 3)
    (hcls : hitClass f.graph.1 g.graph.1 n i = 2) :
    leftRow f.graph.1 g.graph.1 (xChain j2 n i) =
      [if i = 0 then yPlain n else yChain j2 n (i - 1), yChain j2 n i] := by
  rcases hj2 with rfl | rfl <;>
    rw [leftRow_xChain _ _ _ n i (by omega)] <;>
    simp [hcls]

/-- **Upward chain**: from the base spec match, the lane-`b` chain matches climb
to just below the hit index. -/
theorem upward_chain {b m n : ℕ}
    (hM : (gadgetBigraph h f g).IsPerfectMatching M) (hb : b < 2)
    (hcls : ∀ i, i ≠ m → hitClass f.graph.1 g.graph.1 n i = 2)
    (hbase : M.MapsTo (xPlain n) (ySpec b n)) :
    ∀ i, i < m → M.MapsTo (xChain b n i) (yChain b n i) := by
  intro i
  induction i with
  | zero =>
    intro h0
    have hocc : M.MapsTo (xPlain n) (yAt b n 0) := by
      rw [yAt_zero]
      exact hbase
    exact forced_left_snd hM (lane_row hb (hcls 0 (by omega))) hocc
      (xPlain_ne_xChain n b n 0)
  | succ k ih =>
    intro hk
    have hocc : M.MapsTo (xChain b n k) (yAt b n (k + 1)) := by
      rw [yAt_succ]
      exact ih (by omega)
    refine forced_left_snd hM (lane_row hb (hcls (k + 1) (by omega))) hocc ?_
    intro hEq
    obtain ⟨-, -, hik⟩ := xChain_injective (by omega) (by omega) hEq
    omega

/-- **The turn**: the descending-lane vertex at the hit index has the occupied
spec-lane entry as its second neighbor, so it is forced onto the descending
entry (or straight onto `yₙ` when the hit is at index zero). -/
theorem turn_chain {b j2 m n : ℕ}
    (hM : (gadgetBigraph h f g).IsPerfectMatching M)
    (hb : b < 2) (hj2 : j2 = 2 ∨ j2 = 3)
    (hrow : leftRow f.graph.1 g.graph.1 (xChain j2 n m) =
      [if m = 0 then yPlain n else yChain j2 n (m - 1), yAt b n m])
    (hcls : ∀ i, i ≠ m → hitClass f.graph.1 g.graph.1 n i = 2)
    (hbase : M.MapsTo (xPlain n) (ySpec b n)) :
    M.MapsTo (xChain j2 n m) (if m = 0 then yPlain n else yChain j2 n (m - 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hocc : M.MapsTo (xPlain n) (yAt b n 0) := by
      rw [yAt_zero]
      exact hbase
    exact forced_left_snd hM hrow hocc (xPlain_ne_xChain n j2 n 0)
  · have hocc : M.MapsTo (xChain b n (m - 1)) (yAt b n m) := by
      rw [show m = (m - 1) + 1 by omega, yAt_succ]
      exact upward_chain hM hb hcls hbase (m - 1) (by omega)
    refine forced_left_snd hM hrow hocc ?_
    intro hEq
    obtain ⟨hbj, -, -⟩ := xChain_injective (by omega) (by omega) hEq
    omega

/-- **Downward chain**: a descending-lane match at any height forces the
terminal match `(x^{j₂}ₙ,₀, yₙ)` at height zero. -/
theorem downward_chain {j2 m n : ℕ}
    (hM : (gadgetBigraph h f g).IsPerfectMatching M)
    (hj2 : j2 = 2 ∨ j2 = 3)
    (hcls : ∀ i, i ≠ m → hitClass f.graph.1 g.graph.1 n i = 2) :
    ∀ k, k ≤ m →
      M.MapsTo (xChain j2 n k) (if k = 0 then yPlain n else yChain j2 n (k - 1)) →
      M.MapsTo (xChain j2 n 0) (yPlain n) := by
  intro k
  induction k with
  | zero =>
    intro _ hstep
    simpa using hstep
  | succ k' ih =>
    intro hk hstep
    rw [if_neg (by omega), Nat.add_sub_cancel] at hstep
    refine ih (by omega) ?_
    have hrow := desc_row (n := n) (i := k') hj2 (hcls k' (by omega))
    refine forced_left_snd hM hrow hstep ?_
    intro hEq
    obtain ⟨-, -, hik⟩ := xChain_injective (by omega) (by omega) hEq
    omega

/-! ### The two truth-table cases and the reversal headline -/

/-- **The `f` case**: an `f`-hit lands in the separator — base dichotomy, the
matching lane's turn at class `0`, descent to the terminal, and the matching
disjunct of `separatorSet`. -/
theorem separator_mem_of_f (hM : (gadgetBigraph h f g).IsPerfectMatching M)
    (hfi : f.IsInjective) (hdisj : DisjointRanges f g)
    {m n : ℕ} (hm : f.MapsTo m n) : n ∈ separatorSet M.graph.1 := by
  have hcls : ∀ i, i ≠ m → hitClass f.graph.1 g.graph.1 n i = 2 := fun i hi => by
    rw [class_of_f hfi hdisj hm i, if_neg hi]
  have hclsm : hitClass f.graph.1 g.graph.1 n m = 0 := by
    rw [class_of_f hfi hdisj hm m, if_pos rfl]
  obtain ⟨w, hw, hwrow⟩ := matched_left hM (xPlain n)
  rw [leftRow_xPlain] at hwrow
  rcases mem_pair''.mp hwrow with rfl | rfl
  · have hrow : leftRow f.graph.1 g.graph.1 (xChain 2 n m)
        = [if m = 0 then yPlain n else yChain 2 n (m - 1), yAt 0 n m] := by
      rw [leftRow_xChain _ _ 2 n m (by omega)]
      simp [hclsm]
    have hturn := turn_chain hM (by omega) (Or.inl rfl) hrow hcls hw
    exact Or.inl ⟨hw, downward_chain hM (Or.inl rfl) hcls m le_rfl hturn⟩
  · have hrow : leftRow f.graph.1 g.graph.1 (xChain 3 n m)
        = [if m = 0 then yPlain n else yChain 3 n (m - 1), yAt 1 n m] := by
      rw [leftRow_xChain _ _ 3 n m (by omega)]
      simp [hclsm]
    have hturn := turn_chain hM (by omega) (Or.inr rfl) hrow hcls hw
    exact Or.inr ⟨hw, downward_chain hM (Or.inr rfl) hcls m le_rfl hturn⟩

/-- **The `g` case**: a `g`-hit stays out of the separator — the class-`1` turn
sends the OPPOSITE descending lane onto `yₙ`, and both `separatorSet` disjuncts
then fail (one by matching injectivity on `yₙ`, the other by functionality at
`xₙ`). -/
theorem separator_notMem_of_g (hM : (gadgetBigraph h f g).IsPerfectMatching M)
    (hgi : g.IsInjective) (hdisj : DisjointRanges f g)
    {m n : ℕ} (hm : g.MapsTo m n) : n ∉ separatorSet M.graph.1 := by
  have hcls : ∀ i, i ≠ m → hitClass f.graph.1 g.graph.1 n i = 2 := fun i hi => by
    rw [class_of_g hgi hdisj hm i, if_neg hi]
  have hclsm : hitClass f.graph.1 g.graph.1 n m = 1 := by
    rw [class_of_g hgi hdisj hm m, if_pos rfl]
  obtain ⟨w, hw, hwrow⟩ := matched_left hM (xPlain n)
  rw [leftRow_xPlain] at hwrow
  rcases mem_pair''.mp hwrow with rfl | rfl
  · -- base lane 0: the class-1 turn rides lane 3 onto yₙ
    have hrow : leftRow f.graph.1 g.graph.1 (xChain 3 n m)
        = [if m = 0 then yPlain n else yChain 3 n (m - 1), yAt 0 n m] := by
      rw [leftRow_xChain _ _ 3 n m (by omega)]
      simp [hclsm]
    have hterm := downward_chain hM (Or.inr rfl) hcls m le_rfl
      (turn_chain hM (by omega) (Or.inr rfl) hrow hcls hw)
    rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · have hEq := hM.2.1 (xChain 2 n 0) (xChain 3 n 0) (yPlain n) h2 hterm
      obtain ⟨hj, -, -⟩ := xChain_injective (by omega) (by omega) hEq
      omega
    · have hEq := M.singleValued (xPlain n) _ _ h1 hw
      obtain ⟨hb, -⟩ := ySpec_injective (by omega) (by omega) hEq
      omega
  · -- base lane 1: the class-1 turn rides lane 2 onto yₙ
    have hrow : leftRow f.graph.1 g.graph.1 (xChain 2 n m)
        = [if m = 0 then yPlain n else yChain 2 n (m - 1), yAt 1 n m] := by
      rw [leftRow_xChain _ _ 2 n m (by omega)]
      simp [hclsm]
    have hterm := downward_chain hM (Or.inl rfl) hcls m le_rfl
      (turn_chain hM (by omega) (Or.inl rfl) hrow hcls hw)
    rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · have hEq := M.singleValued (xPlain n) _ _ h1 hw
      obtain ⟨hb, -⟩ := ySpec_injective (by omega) (by omega) hEq
      omega
    · have hEq := hM.2.1 (xChain 3 n 0) (xChain 2 n 0) (yPlain n) h2 hterm
      obtain ⟨hj, -, -⟩ := xChain_injective (by omega) (by omega) hEq
      omega

end ForcedChains

end SeparationGadget

open SeparationGadget in
/-- **The reversal's first leg** (Shafer Thm 6.1.2 (v) ⇒ separation): over a
Turing ideal, 2-regular perfect matching yields disjoint-range separation —
instantiate the capability at the gadget, decode the separator, and run the two
forced-chain cases. -/
theorem matching_separates {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (hmatch : TwoRegularPerfectMatchingAt Ω) : DisjointRangeSeparationAt Ω := by
  intro f g hfi hgi hdisj
  obtain ⟨M, hM⟩ := hmatch (gadgetBigraph h f g)
  exact ⟨gadgetSeparator h M,
    fun m v hmv => separator_mem_of_f hM hfi hdisj hmv,
    fun m v hmv => separator_notMem_of_g hM hgi hdisj hmv⟩

end ReverseMathlib.Omega
