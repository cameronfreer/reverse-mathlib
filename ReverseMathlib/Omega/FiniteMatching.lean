/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite

/-!
# The finite symmetric-Hall covering lemma (issue #42, slice 2)

The finite combinatorics feeding the 2-regular matching compiler's level
nonemptiness, following Shafer (thesis, §6.1) Lemma 6.1.5 and the degree-counting
base of Lemma 6.1.6:

* `exists_matching_covering` — a finite bipartite graph with Hall's condition on
  all subsets of a distinguished left set `A₀` AND all subsets of a distinguished
  right set `B₀` has a matching covering `A₀ ∪ B₀`. Induction on `A₀.card + B₀.card`
  with Shafer's three cases: no `A₀`–`B₀` edge (finite Hall twice, into disjoint
  targets), everything slack (delete one `A₀`–`B₀` edge pair), or a tight set
  (finite Hall matches it off perfectly, Hall survives on the rest).
* `hall_of_degree_le_two` — the counting argument: degree ≤ 2 everywhere plus
  degree exactly 2 on the distinguished set yields Hall's condition on its subsets
  (`2·|S|` edge-endpoints land in `N(S)`, each absorbing at most two).

Everything is stated on an explicit edge `Finset (ℕ × ℕ)`; mathlib's **finite**
Hall theorem (`Finset.all_card_le_biUnion_card_iff_existsInjective'`,
`Mathlib/Combinatorics/Hall/Finite.lean`) is the only matching input — the
infinite Hall theorem and its compactness boundary never enter (route gates in
`scripts/MetaSmoke.lean` pin this for the compiled direction).
-/

assert_not_exists Finset.all_card_le_biUnion_card_iff_exists_injective

namespace ReverseMathlib.Omega

open Finset

/-- The right-neighbors of left vertex `a` in the edge set `E`. -/
def rightNbrs (E : Finset (ℕ × ℕ)) (a : ℕ) : Finset ℕ :=
  (E.filter fun p => p.1 = a).image Prod.snd

/-- The left-neighbors of right vertex `b` in the edge set `E`. -/
def leftNbrs (E : Finset (ℕ × ℕ)) (b : ℕ) : Finset ℕ :=
  (E.filter fun p => p.2 = b).image Prod.fst

theorem mem_rightNbrs {E : Finset (ℕ × ℕ)} {a b : ℕ} :
    b ∈ rightNbrs E a ↔ (a, b) ∈ E := by
  simp only [rightNbrs, mem_image, mem_filter, Prod.exists]
  constructor
  · rintro ⟨a', b', ⟨hE, rfl⟩, rfl⟩
    exact hE
  · exact fun h => ⟨a, b, ⟨h, rfl⟩, rfl⟩

theorem mem_leftNbrs {E : Finset (ℕ × ℕ)} {a b : ℕ} :
    a ∈ leftNbrs E b ↔ (a, b) ∈ E := by
  simp only [leftNbrs, mem_image, mem_filter, Prod.exists]
  constructor
  · rintro ⟨a', b', ⟨hE, rfl⟩, rfl⟩
    exact hE
  · exact fun h => ⟨a, b, ⟨h, rfl⟩, rfl⟩

/-- `M` is a matching: no two distinct edges share an endpoint on either side. -/
def IsMatchingSet (M : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2

/-- `M` covers `A₀` on the left and `B₀` on the right. -/
def CoversSides (M : Finset (ℕ × ℕ)) (A₀ B₀ : Finset ℕ) : Prop :=
  (∀ a ∈ A₀, ∃ b, (a, b) ∈ M) ∧ ∀ b ∈ B₀, ∃ a, (a, b) ∈ M

/-- Finite Hall on a `Finset` of indices, packaged: Hall's condition on all subsets
of `X` yields an injective-on-`X` choice into the neighbor sets. The only matching
input of this file — mathlib's finite Hall theorem over the `Fintype` index `↥X`. -/
private theorem exists_injOn_choice {t : ℕ → Finset ℕ} {X : Finset ℕ}
    (hall : ∀ S ⊆ X, S.card ≤ (S.biUnion t).card) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑X ∧ ∀ a ∈ X, f a ∈ t a := by
  classical
  have hall' : ∀ s : Finset ↥X, s.card ≤ (s.biUnion fun x => t x.1).card := by
    intro s
    have himg : (s.image Subtype.val).biUnion t = s.biUnion fun x => t x.1 := by
      ext y
      simp [mem_biUnion]
    have hsub : s.image Subtype.val ⊆ X := by
      intro a ha
      obtain ⟨x, -, rfl⟩ := mem_image.mp ha
      exact x.2
    have := hall (s.image Subtype.val) hsub
    rwa [card_image_of_injective s Subtype.val_injective, himg] at this
  obtain ⟨f', hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' fun x : ↥X => t x.1).mp hall'
  refine ⟨fun a => if h : a ∈ X then f' ⟨a, h⟩ else 0, ?_, ?_⟩
  · intro a ha a' ha' hEq
    have ha'' : a ∈ X := ha
    have ha''' : a' ∈ X := ha'
    simp only [dif_pos ha'', dif_pos ha'''] at hEq
    exact congrArg Subtype.val (hinj hEq)
  · intro a ha
    simp only [dif_pos ha]
    exact hmem ⟨a, ha⟩

/-- **Degree counting** (Shafer's Lemma 6.1.6 base, at degree two): degree at most
two on the co-side plus degree exactly two on the distinguished set yields Hall's
condition on its subsets — `2·|S|` edge-endpoints land in `N(S)`, each vertex of
which absorbs at most two. Stated for the left side; apply to the swapped edge set
for the right side. -/
theorem hall_of_degree_le_two {E : Finset (ℕ × ℕ)} {A₀ : Finset ℕ}
    (hdeg2 : ∀ a ∈ A₀, (rightNbrs E a).card = 2)
    (hright : ∀ b, (leftNbrs E b).card ≤ 2) :
    ∀ S ⊆ A₀, S.card ≤ (S.biUnion (rightNbrs E)).card := by
  classical
  intro S hS
  set NS := S.biUnion (rightNbrs E) with hNS
  set ES := E.filter fun p => p.1 ∈ S with hES
  have hcount1 : ES.card = ∑ a ∈ S, (rightNbrs E a).card := by
    have h := card_eq_sum_card_fiberwise (f := Prod.fst)
      (s := E.filter fun p => p.1 ∈ S) (t := S) (fun p hp => (mem_filter.mp hp).2)
    rw [hES, h]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hfib : (E.filter fun p => p.1 ∈ S).filter (fun p => p.1 = a)
        = E.filter fun p => p.1 = a := by
      ext p
      simp only [Finset.filter_filter, mem_filter]
      constructor
      · rintro ⟨hE, -, h1⟩
        exact ⟨hE, h1⟩
      · rintro ⟨hE, h1⟩
        exact ⟨hE, h1 ▸ ha, h1⟩
    rw [hfib, rightNbrs, Finset.card_image_of_injOn fun p hp q hq hpq =>
      Prod.ext (((mem_filter.mp (Finset.mem_coe.mp hp)).2).trans
        ((mem_filter.mp (Finset.mem_coe.mp hq)).2).symm) hpq]
  have hcount2 : ES.card = ∑ b ∈ NS, (ES.filter fun p => p.2 = b).card := by
    refine card_eq_sum_card_fiberwise (f := Prod.snd) (t := NS) fun p hp => ?_
    obtain ⟨hE, hS'⟩ := mem_filter.mp hp
    exact mem_biUnion.mpr ⟨p.1, hS', mem_rightNbrs.mpr (by simpa using hE)⟩
  have hfiber : ∀ b, (ES.filter fun p => p.2 = b).card ≤ 2 := by
    intro b
    refine le_trans (card_le_card_of_injOn Prod.fst ?_ ?_) (hright b)
    · intro p hp
      obtain ⟨hpES, hpb⟩ := mem_filter.mp hp
      obtain ⟨hpE, -⟩ := mem_filter.mp hpES
      refine mem_leftNbrs.mpr ?_
      rw [← hpb]
      simpa using hpE
    · intro p hp q hq hpq
      have h1 := (mem_filter.mp (Finset.mem_coe.mp hp)).2
      have h2 := (mem_filter.mp (Finset.mem_coe.mp hq)).2
      exact Prod.ext hpq (h1.trans h2.symm)
  have hlhs : 2 * S.card ≤ ES.card := by
    rw [hcount1]
    calc 2 * S.card = ∑ _a ∈ S, 2 := by
          rw [Finset.sum_const_nat fun _ _ => rfl, mul_comm]
      _ ≤ ∑ a ∈ S, (rightNbrs E a).card :=
          Finset.sum_le_sum fun a ha => (hdeg2 a (hS ha)).ge
  have hrhs : ES.card ≤ 2 * NS.card := by
    rw [hcount2]
    calc ∑ b ∈ NS, (ES.filter fun p => p.2 = b).card ≤ ∑ _b ∈ NS, 2 :=
        Finset.sum_le_sum fun b _ => hfiber b
      _ = 2 * NS.card := by rw [Finset.sum_const_nat fun _ _ => rfl, mul_comm]
  omega

/-- The tight-set step, shared by both sides via edge swapping in the caller: given a
nonempty tight `S ⊆ A₀`, finite Hall matches `S` perfectly onto its neighborhood, and
Hall's condition survives on the graph with `S` and its neighborhood removed. Returns
the perfect part and the reduced data; the caller recurses on the reduced graph. -/
private theorem tight_step {E : Finset (ℕ × ℕ)} {A₀ B₀ S : Finset ℕ}
    (hallA : ∀ T ⊆ A₀, T.card ≤ (T.biUnion (rightNbrs E)).card)
    (hallB : ∀ T ⊆ B₀, T.card ≤ (T.biUnion (leftNbrs E)).card)
    (hSA : S ⊆ A₀) (htight : (S.biUnion (rightNbrs E)).card = S.card) :
    ∃ M₁ ⊆ E, IsMatchingSet M₁ ∧ (∀ a ∈ S, ∃ b, (a, b) ∈ M₁) ∧
      (∀ b ∈ S.biUnion (rightNbrs E), ∃ a, (a, b) ∈ M₁) ∧
      (∀ p ∈ M₁, p.1 ∈ S ∧ p.2 ∈ S.biUnion (rightNbrs E)) ∧
      (∀ T ⊆ A₀ \ S, T.card ≤
        (T.biUnion (rightNbrs (E.filter fun p =>
          p.1 ∉ S ∧ p.2 ∉ S.biUnion (rightNbrs E)))).card) ∧
      ∀ T ⊆ B₀ \ S.biUnion (rightNbrs E), T.card ≤
        (T.biUnion (leftNbrs (E.filter fun p =>
          p.1 ∉ S ∧ p.2 ∉ S.biUnion (rightNbrs E)))).card := by
  classical
  set NS := S.biUnion (rightNbrs E) with hNS
  set H := E.filter fun p => p.1 ∉ S ∧ p.2 ∉ NS with hH
  obtain ⟨f, hfinj, hfmem⟩ := exists_injOn_choice fun T hT => hallA T (hT.trans hSA)
  have himg : S.image f = NS := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact mem_biUnion.mpr ⟨x, hx, hfmem x hx⟩
    · rw [Finset.card_image_of_injOn hfinj, htight]
  refine ⟨S.image fun x => (x, f x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
    exact mem_rightNbrs.mp (hfmem x hx)
  · intro p hp q hq hne
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
    obtain ⟨x', hx', rfl⟩ := mem_image.mp hq
    have hxx : x ≠ x' := fun h => hne (h ▸ rfl)
    exact ⟨hxx, fun h => hxx (hfinj hx hx' h)⟩
  · exact fun a ha => ⟨f a, mem_image.mpr ⟨a, ha, rfl⟩⟩
  · intro b hb
    have : b ∈ S.image f := himg ▸ hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp this
    exact ⟨x, mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
    exact ⟨hx, mem_biUnion.mpr ⟨x, hx, hfmem x hx⟩⟩
  · intro T hT
    by_contra hlt
    push Not at hlt
    have hTS : ∀ t ∈ T, t ∉ S := fun t ht => (mem_sdiff.mp (hT ht)).2
    have hbi : T.biUnion (rightNbrs H) = (T.biUnion (rightNbrs E)) \ NS := by
      ext y
      simp only [mem_biUnion, mem_sdiff]
      constructor
      · rintro ⟨t, htT, hty⟩
        have := mem_filter.mp (mem_rightNbrs.mp hty)
        exact ⟨⟨t, htT, mem_rightNbrs.mpr this.1⟩, this.2.2⟩
      · rintro ⟨⟨t, htT, hty⟩, hyNS⟩
        exact ⟨t, htT, mem_rightNbrs.mpr
          (mem_filter.mpr ⟨mem_rightNbrs.mp hty, hTS t htT, hyNS⟩)⟩
    have hsub2 : (T ∪ S).biUnion (rightNbrs E) ⊆ (T.biUnion (rightNbrs H)) ∪ NS := by
      intro y hy
      obtain ⟨t, htT, hty⟩ := mem_biUnion.mp hy
      rcases mem_union.mp htT with htT | htS
      · by_cases hyNS : y ∈ NS
        · exact mem_union_right _ hyNS
        · exact mem_union_left _ (mem_biUnion.mpr ⟨t, htT, mem_rightNbrs.mpr
            (mem_filter.mpr ⟨mem_rightNbrs.mp hty, hTS t htT, hyNS⟩)⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨t, htS, hty⟩)
    have hTSsub : T ∪ S ⊆ A₀ := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_sdiff.mp (hT hx)).1
      · exact hSA hx
    have hdisj : Disjoint T S :=
      Finset.disjoint_left.mpr fun x hx => (mem_sdiff.mp (hT hx)).2
    have h1 := hallA (T ∪ S) hTSsub
    have h2 := (card_le_card hsub2).trans (card_union_le _ _)
    rw [card_union_of_disjoint hdisj] at h1
    omega
  · intro T hT
    have hbi : T.biUnion (leftNbrs H) = T.biUnion (leftNbrs E) := by
      refine Finset.biUnion_congr rfl fun t ht => ?_
      have htNS : t ∉ NS := (mem_sdiff.mp (hT ht)).2
      ext x
      simp only [mem_leftNbrs, hH, mem_filter]
      constructor
      · rintro ⟨hE, -, -⟩
        exact hE
      · intro hE
        refine ⟨hE, fun hxS => htNS ?_, htNS⟩
        exact mem_biUnion.mpr ⟨x, hxS, mem_rightNbrs.mpr hE⟩
    rw [hbi]
    exact hallB T (hT.trans (Finset.sdiff_subset))

/-- Swapping the two sides of the edge set exchanges the neighbor operators. -/
private theorem rightNbrs_swap (E : Finset (ℕ × ℕ)) (b : ℕ) :
    rightNbrs (E.image Prod.swap) b = leftNbrs E b := by
  ext a
  rw [mem_rightNbrs, mem_leftNbrs]
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, hswap⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Prod.ext_iff.mp hswap
    exact hxy
  · exact fun h => Finset.mem_image.mpr ⟨(a, b), h, rfl⟩

private theorem leftNbrs_swap (E : Finset (ℕ × ℕ)) (a : ℕ) :
    leftNbrs (E.image Prod.swap) a = rightNbrs E a := by
  ext b
  rw [mem_rightNbrs, mem_leftNbrs]
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, hswap⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Prod.ext_iff.mp hswap
    exact hxy
  · exact fun h => Finset.mem_image.mpr ⟨(a, b), h, rfl⟩

/-- The full tight-set case, parameterized by the induction hypothesis: match the
tight set off perfectly (`tight_step`), recurse on the reduced graph, and assemble.
Shared by both sides — the right-side case applies it to the swapped edge set. -/
private theorem tight_case {N : ℕ}
    (ih : ∀ (E : Finset (ℕ × ℕ)) (A₀ B₀ : Finset ℕ),
      A₀.card + B₀.card ≤ N →
      (∀ S ⊆ A₀, S.card ≤ (S.biUnion (rightNbrs E)).card) →
      (∀ S ⊆ B₀, S.card ≤ (S.biUnion (leftNbrs E)).card) →
      ∃ M ⊆ E, IsMatchingSet M ∧ CoversSides M A₀ B₀)
    {E : Finset (ℕ × ℕ)} {A₀ B₀ S : Finset ℕ}
    (hcard : A₀.card + B₀.card ≤ N + 1)
    (hallA : ∀ T ⊆ A₀, T.card ≤ (T.biUnion (rightNbrs E)).card)
    (hallB : ∀ T ⊆ B₀, T.card ≤ (T.biUnion (leftNbrs E)).card)
    (hSA : S ⊆ A₀) (hSne : S.Nonempty)
    (htight : (S.biUnion (rightNbrs E)).card = S.card) :
    ∃ M ⊆ E, IsMatchingSet M ∧ CoversSides M A₀ B₀ := by
  classical
  obtain ⟨M₁, hM₁E, hM₁match, hM₁covS, hM₁covNS, hM₁supp, hallA', hallB'⟩ :=
    tight_step hallA hallB hSA htight
  set NS := S.biUnion (rightNbrs E) with hNS
  set H := E.filter fun p => p.1 ∉ S ∧ p.2 ∉ NS with hH
  have hcard' : (A₀ \ S).card + (B₀ \ NS).card ≤ N := by
    have h1 : (A₀ \ S).card = A₀.card - S.card := by
      rw [card_sdiff, Finset.inter_eq_left.mpr hSA]
    have h2 : (B₀ \ NS).card ≤ B₀.card := card_le_card Finset.sdiff_subset
    have h3 : 1 ≤ S.card := Finset.card_pos.mpr hSne
    have h4 : S.card ≤ A₀.card := card_le_card hSA
    omega
  obtain ⟨M', hM'H, hM'match, hM'covA, hM'covB⟩ := ih H (A₀ \ S) (B₀ \ NS)
    hcard' hallA' hallB'
  have hM'E : M' ⊆ E := hM'H.trans (Finset.filter_subset _ _)
  have hM'supp : ∀ p ∈ M', p.1 ∉ S ∧ p.2 ∉ NS :=
    fun p hp => (mem_filter.mp (hM'H hp)).2
  refine ⟨M₁ ∪ M', union_subset hM₁E hM'E, ?_, ?_, ?_⟩
  · intro p hp q hq hne
    rcases mem_union.mp hp with hp | hp <;> rcases mem_union.mp hq with hq | hq
    · exact hM₁match p hp q hq hne
    · have h1 := hM₁supp p hp
      have h2 := hM'supp q hq
      exact ⟨fun h => h2.1 (h ▸ h1.1), fun h => h2.2 (h ▸ h1.2)⟩
    · have h1 := hM₁supp q hq
      have h2 := hM'supp p hp
      exact ⟨fun h => h2.1 (h.symm ▸ h1.1), fun h => h2.2 (h.symm ▸ h1.2)⟩
    · exact hM'match p hp q hq hne
  · intro a ha
    by_cases haS : a ∈ S
    · obtain ⟨b, hb⟩ := hM₁covS a haS
      exact ⟨b, mem_union_left _ hb⟩
    · obtain ⟨b, hb⟩ := hM'covA a (mem_sdiff.mpr ⟨ha, haS⟩)
      exact ⟨b, mem_union_right _ hb⟩
  · intro b hb
    by_cases hbNS : b ∈ NS
    · obtain ⟨a, ha⟩ := hM₁covNS b hbNS
      exact ⟨a, mem_union_left _ ha⟩
    · obtain ⟨a, ha⟩ := hM'covB b (mem_sdiff.mpr ⟨hb, hbNS⟩)
      exact ⟨a, mem_union_right _ ha⟩

/-- The right-side counting corollary, through the swapped edge set. -/
theorem hall_of_degree_le_two_right {E : Finset (ℕ × ℕ)} {B₀ : Finset ℕ}
    (hdeg2 : ∀ b ∈ B₀, (leftNbrs E b).card = 2)
    (hleft : ∀ a, (rightNbrs E a).card ≤ 2) :
    ∀ S ⊆ B₀, S.card ≤ (S.biUnion (leftNbrs E)).card := by
  intro S hS
  have h := hall_of_degree_le_two (E := E.image Prod.swap) (A₀ := B₀)
    (fun b hb => by rw [rightNbrs_swap]; exact hdeg2 b hb)
    (fun a => by rw [leftNbrs_swap]; exact hleft a) S hS
  rwa [Finset.biUnion_congr rfl fun t _ => rightNbrs_swap E t] at h

/-- **The finite symmetric-Hall covering lemma** (Shafer's Lemma 6.1.5): a finite
bipartite graph with Hall's condition on all subsets of the distinguished left set
`A₀` and on all subsets of the distinguished right set `B₀` has one matching
covering `A₀ ∪ B₀`. Induction on `A₀.card + B₀.card` with Shafer's three cases: no
`A₀`–`B₀` edge (finite Hall on each side, into disjoint targets); a tight set on
either side (`tight_case`, applied to the swapped edge set for a right-side tight
set); otherwise everything is slack and one `A₀`–`B₀` edge pair is deleted. -/
theorem exists_matching_covering (E : Finset (ℕ × ℕ)) (A₀ B₀ : Finset ℕ)
    (hallA : ∀ S ⊆ A₀, S.card ≤ (S.biUnion (rightNbrs E)).card)
    (hallB : ∀ S ⊆ B₀, S.card ≤ (S.biUnion (leftNbrs E)).card) :
    ∃ M ⊆ E, IsMatchingSet M ∧ CoversSides M A₀ B₀ := by
  classical
  suffices h : ∀ N (E : Finset (ℕ × ℕ)) (A₀ B₀ : Finset ℕ),
      A₀.card + B₀.card ≤ N →
      (∀ S ⊆ A₀, S.card ≤ (S.biUnion (rightNbrs E)).card) →
      (∀ S ⊆ B₀, S.card ≤ (S.biUnion (leftNbrs E)).card) →
      ∃ M ⊆ E, IsMatchingSet M ∧ CoversSides M A₀ B₀ from
    h _ E A₀ B₀ le_rfl hallA hallB
  clear hallA hallB E A₀ B₀
  intro N
  induction N with
  | zero =>
    intro E A₀ B₀ hcard _ _
    have hA : A₀ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hB : B₀ = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hA
    subst hB
    refine ⟨∅, Finset.empty_subset E, ?_, ?_, ?_⟩
    · intro p hp
      exact absurd hp (Finset.notMem_empty p)
    · intro a ha
      exact absurd ha (Finset.notMem_empty a)
    · intro b hb
      exact absurd hb (Finset.notMem_empty b)
  | succ N ih =>
    intro E A₀ B₀ hcard hallA hallB
    by_cases hedge : ∃ a ∈ A₀, ∃ b ∈ B₀, (a, b) ∈ E
    · by_cases htA : ∃ S ⊆ A₀, S.Nonempty ∧ (S.biUnion (rightNbrs E)).card = S.card
      · obtain ⟨S, hSA, hSne, htight⟩ := htA
        exact tight_case ih hcard hallA hallB hSA hSne htight
      · by_cases htB : ∃ S ⊆ B₀, S.Nonempty ∧ (S.biUnion (leftNbrs E)).card = S.card
        · -- a tight right set: the same case on the swapped edge set, then unswap
          obtain ⟨S, hSB, hSne, htight⟩ := htB
          have hallA₂ : ∀ T ⊆ B₀, T.card ≤
              (T.biUnion (rightNbrs (E.image Prod.swap))).card := by
            intro T hT
            rw [Finset.biUnion_congr rfl fun t _ => rightNbrs_swap E t]
            exact hallB T hT
          have hallB₂ : ∀ T ⊆ A₀, T.card ≤
              (T.biUnion (leftNbrs (E.image Prod.swap))).card := by
            intro T hT
            rw [Finset.biUnion_congr rfl fun t _ => leftNbrs_swap E t]
            exact hallA T hT
          have htight₂ : (S.biUnion (rightNbrs (E.image Prod.swap))).card = S.card := by
            rw [Finset.biUnion_congr rfl fun t _ => rightNbrs_swap E t]
            exact htight
          obtain ⟨M, hME, hMmatch, hMcov⟩ := tight_case ih (by omega) hallA₂ hallB₂
            hSB hSne htight₂
          refine ⟨M.image Prod.swap, ?_, ?_, ?_, ?_⟩
          · intro p hp
            obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
            obtain ⟨r, hr, rfl⟩ := mem_image.mp (hME hq)
            simpa [Prod.swap_swap] using hr
          · intro p hp q hq hne
            obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
            obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hq
            have hne₀ : p₀ ≠ q₀ := fun h => hne (h ▸ rfl)
            have := hMmatch p₀ hp₀ q₀ hq₀ hne₀
            exact ⟨this.2, this.1⟩
          · intro a ha
            obtain ⟨x, hx⟩ := hMcov.2 a ha
            exact ⟨x, mem_image.mpr ⟨(x, a), hx, rfl⟩⟩
          · intro b hb
            obtain ⟨y, hy⟩ := hMcov.1 b hb
            exact ⟨y, mem_image.mpr ⟨(b, y), hy, rfl⟩⟩
        · -- everything slack: delete one A₀–B₀ edge pair
          obtain ⟨a, haA, b, hbB, hab⟩ := hedge
          push Not at htA htB
          set E' := E.filter fun p => p.1 ≠ a ∧ p.2 ≠ b with hE'
          have hallA' : ∀ T ⊆ A₀.erase a,
              T.card ≤ (T.biUnion (rightNbrs E')).card := by
            intro T hT
            rcases T.eq_empty_or_nonempty with rfl | hTne
            · simp
            have hTA : T ⊆ A₀ := hT.trans (Finset.erase_subset _ _)
            have hslack : T.card + 1 ≤ (T.biUnion (rightNbrs E)).card := by
              have h1 := hallA T hTA
              have h2 := htA T hTA hTne
              omega
            have hsup : (T.biUnion (rightNbrs E)).erase b ⊆
                T.biUnion (rightNbrs E') := by
              intro y hy
              obtain ⟨hyb, hyE⟩ := mem_erase.mp hy
              obtain ⟨t, htT, hty⟩ := mem_biUnion.mp hyE
              exact mem_biUnion.mpr ⟨t, htT, mem_rightNbrs.mpr (mem_filter.mpr
                ⟨mem_rightNbrs.mp hty, ne_of_mem_erase (hT htT), hyb⟩)⟩
            have h3 := card_le_card hsup
            have h4 : (T.biUnion (rightNbrs E)).card - 1 ≤
                ((T.biUnion (rightNbrs E)).erase b).card :=
              Finset.pred_card_le_card_erase
            omega
          have hallB' : ∀ T ⊆ B₀.erase b,
              T.card ≤ (T.biUnion (leftNbrs E')).card := by
            intro T hT
            rcases T.eq_empty_or_nonempty with rfl | hTne
            · simp
            have hTB : T ⊆ B₀ := hT.trans (Finset.erase_subset _ _)
            have hslack : T.card + 1 ≤ (T.biUnion (leftNbrs E)).card := by
              have h1 := hallB T hTB
              have h2 := htB T hTB hTne
              omega
            have hsup : (T.biUnion (leftNbrs E)).erase a ⊆
                T.biUnion (leftNbrs E') := by
              intro y hy
              obtain ⟨hya, hyE⟩ := mem_erase.mp hy
              obtain ⟨t, htT, hty⟩ := mem_biUnion.mp hyE
              exact mem_biUnion.mpr ⟨t, htT, mem_leftNbrs.mpr (mem_filter.mpr
                ⟨mem_leftNbrs.mp hty, hya, ne_of_mem_erase (hT htT)⟩)⟩
            have h3 := card_le_card hsup
            have h4 : (T.biUnion (leftNbrs E)).card - 1 ≤
                ((T.biUnion (leftNbrs E)).erase a).card :=
              Finset.pred_card_le_card_erase
            omega
          have hcard' : (A₀.erase a).card + (B₀.erase b).card ≤ N := by
            rw [Finset.card_erase_of_mem haA, Finset.card_erase_of_mem hbB]
            have h1 : 1 ≤ A₀.card := Finset.card_pos.mpr ⟨a, haA⟩
            have h2 : 1 ≤ B₀.card := Finset.card_pos.mpr ⟨b, hbB⟩
            omega
          obtain ⟨M', hM'E', hM'match, hM'covA, hM'covB⟩ := ih E' (A₀.erase a)
            (B₀.erase b) hcard' hallA' hallB'
          have hM'supp : ∀ p ∈ M', p.1 ≠ a ∧ p.2 ≠ b :=
            fun p hp => (mem_filter.mp (hM'E' hp)).2
          refine ⟨insert (a, b) M', ?_, ?_, ?_, ?_⟩
          · intro p hp
            rcases mem_insert.mp hp with rfl | hp
            · exact hab
            · exact (hM'E'.trans (Finset.filter_subset _ _)) hp
          · intro p hp q hq hne
            rcases mem_insert.mp hp with rfl | hp <;>
              rcases mem_insert.mp hq with rfl | hq
            · exact absurd rfl hne
            · have h := hM'supp q hq
              exact ⟨fun hh => h.1 hh.symm, fun hh => h.2 hh.symm⟩
            · have h := hM'supp p hp
              exact ⟨h.1, h.2⟩
            · exact hM'match p hp q hq hne
          · intro x hx
            by_cases hxa : x = a
            · exact ⟨b, hxa ▸ mem_insert_self _ _⟩
            · obtain ⟨y, hy⟩ := hM'covA x (mem_erase.mpr ⟨hxa, hx⟩)
              exact ⟨y, mem_insert_of_mem hy⟩
          · intro y hy
            by_cases hyb : y = b
            · exact ⟨a, hyb ▸ mem_insert_self _ _⟩
            · obtain ⟨x, hx⟩ := hM'covB y (mem_erase.mpr ⟨hyb, hy⟩)
              exact ⟨x, mem_insert_of_mem hx⟩
    · -- no A₀–B₀ edge: finite Hall on each side, into disjoint targets
      push Not at hedge
      obtain ⟨f, hfinj, hfmem⟩ := exists_injOn_choice hallA
      obtain ⟨g, hginj, hgmem⟩ := exists_injOn_choice hallB
      have hga : ∀ y ∈ B₀, g y ∉ A₀ := by
        intro y hy hgA
        exact hedge (g y) hgA y hy (mem_leftNbrs.mp (hgmem y hy))
      have hfb : ∀ x ∈ A₀, f x ∉ B₀ := by
        intro x hx hfB
        exact hedge x hx (f x) hfB (mem_rightNbrs.mp (hfmem x hx))
      refine ⟨(A₀.image fun x => (x, f x)) ∪ B₀.image fun y => (g y, y),
        ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases mem_union.mp hp with hp | hp
        · obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
          exact mem_rightNbrs.mp (hfmem x hx)
        · obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
          exact mem_leftNbrs.mp (hgmem y hy)
      · intro p hp q hq hne
        rcases mem_union.mp hp with hp | hp <;> rcases mem_union.mp hq with hq | hq
        · obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
          obtain ⟨x', hx', rfl⟩ := mem_image.mp hq
          have hxx : x ≠ x' := fun h => hne (h ▸ rfl)
          exact ⟨hxx, fun h => hxx (hfinj hx hx' h)⟩
        · obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
          obtain ⟨y, hy, rfl⟩ := mem_image.mp hq
          constructor
          · intro h
            have h' : x = g y := h
            exact hga y hy (h' ▸ hx)
          · intro h
            have h' : f x = y := h
            exact hfb x hx (h'.symm ▸ hy)
        · obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
          constructor
          · intro h
            have h' : g y = x := h
            exact hga y hy (h'.symm ▸ hx)
          · intro h
            have h' : y = f x := h
            exact hfb x hx (h' ▸ hy)
        · obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
          obtain ⟨y', hy', rfl⟩ := mem_image.mp hq
          have hyy : y ≠ y' := fun h => hne (h ▸ rfl)
          exact ⟨fun h => hyy (hginj hy hy' h), hyy⟩
      · exact fun x hx => ⟨f x, mem_union_left _ (mem_image.mpr ⟨x, hx, rfl⟩)⟩
      · exact fun y hy => ⟨g y, mem_union_right _ (mem_image.mpr ⟨y, hy, rfl⟩)⟩

end ReverseMathlib.Omega
