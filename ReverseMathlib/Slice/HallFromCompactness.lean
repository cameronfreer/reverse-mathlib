/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.List
import ReverseMathlib.Standard.Hall
import ReverseMathlib.Standard.InverseLimit

/-!
# Countable Hall from explicit finite inverse-limit compactness

The relative theorem of the Hall walking slice:
`countableHall_of_finiteInverseLimitCompactness` derives `Standard.CountableHall` from
`Standard.ExplicitFiniteInverseLimitCompactness` **taken as a hypothesis**. The compactness
principle is never proved here; the point is the factorization of the proof term, certified by
the hard dependency assertions in `scripts/MetaSmoke.lean`.

Mined architecture (from mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`,
`Mathlib/Combinatorics/Hall/Basic.lean`): finite matchings on initial segments are assembled
into a sequential inverse system whose sections are transversals. What is **replaced**: the
categorical/topological compactness boundary — `nonempty_sections_of_finite_inverse_system`,
which routes through `CofilteredSystem` and topological Kőnig (ultimately Tychonoff) — and the
`Classical.indefiniteDescription` selection of a finite matching, which mathlib needs only to
produce type-level `Nonempty` instances for that machinery. Here the presentation repair is
selection-free: each level is an *explicitly enumerated* `Finset` of encoded partial
transversals, and finite Hall (`Finset.all_card_le_biUnion_card_iff_existsInjective'`,
`Mathlib/Combinatorics/Hall/Finite.lean` — reused, not reinvented) proves it `Finset.Nonempty`
directly. No intermediate matching is ever selected.

Levels are coded: a partial transversal of `t` on `{0, …, n-1}` is the list
`[f 0, …, f (n-1)]`, which is `Nodup` exactly when `f` is injective, and is stored as its
`Encodable.encode` code so that fibers are `Finset ℕ` as `ExplicitFiniteInverseSystem` requires.
-/

assert_not_exists Finset.all_card_le_biUnion_card_iff_exists_injective

namespace ReverseMathlib.Slice

open ReverseMathlib.Standard

/-! ## Candidate lists and level fibers -/

/-- The explicitly enumerated finite set of lists of length `n` whose `i`-th entry lies in
`t i`: partial (not yet injective) transversals on `{0, …, n-1}`, built by recursion with no
selection. -/
def candLists (t : ℕ → Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => ((candLists t n) ×ˢ t n).image fun p => p.1 ++ [p.2]

theorem mem_candLists {t : ℕ → Finset ℕ} : ∀ {n : ℕ} {l : List ℕ},
    l ∈ candLists t n ↔ l.length = n ∧ ∀ i, (hi : i < l.length) → l[i] ∈ t i
  | 0, l => by
    constructor
    · rintro h
      rw [candLists, Finset.mem_singleton] at h
      subst h
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
    · rintro ⟨hlen, -⟩
      rw [candLists, Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero hlen
  | n + 1, l => by
    rw [candLists, Finset.mem_image]
    constructor
    · rintro ⟨⟨l', a⟩, hp, rfl⟩
      rw [Finset.mem_product] at hp
      obtain ⟨hl', ha⟩ := hp
      obtain ⟨hlen, hmem⟩ := mem_candLists.mp hl'
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      rcases Nat.lt_or_ge i l'.length with h | h
      · rw [List.getElem_append_left h]
        exact hmem i h
      · have : i = l'.length := by
          have := List.length_append (as := l') (bs := [a]) ▸ hi
          simp only [List.length_singleton] at this
          omega
        subst this
        simpa [hlen] using ha
    · rintro ⟨hlen, hmem⟩
      have hne : l ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
      have hdlen : l.dropLast.length = n := by simp [hlen]
      have hmem1 : l.dropLast ∈ candLists t n := by
        refine mem_candLists.mpr ⟨hdlen, fun i hi => ?_⟩
        rw [List.getElem_dropLast]
        exact hmem i (by simp at hi; omega)
      have hmem2 : l.getLast hne ∈ t n := by
        have : l.getLast hne = l[n]'(by omega) := by
          rw [List.getLast_eq_getElem]
          simp [hlen]
        rw [this]
        exact hmem n (by omega)
      exact ⟨(l.dropLast, l.getLast hne), Finset.mem_product.mpr ⟨hmem1, hmem2⟩,
        List.dropLast_append_getLast hne⟩

/-- The explicitly enumerated finite set of *injective* partial transversals on
`{0, …, n-1}`, as `Nodup` candidate lists. -/
def transversalLists (t : ℕ → Finset ℕ) (n : ℕ) : Finset (List ℕ) :=
  (candLists t n).filter fun l => l.Nodup

theorem mem_transversalLists {t : ℕ → Finset ℕ} {n : ℕ} {l : List ℕ} :
    l ∈ transversalLists t n ↔
      (l.length = n ∧ ∀ i, (hi : i < l.length) → l[i] ∈ t i) ∧ l.Nodup := by
  rw [transversalLists, Finset.mem_filter, mem_candLists]

/-- Level `n` of the inverse system: codes of the injective partial transversals on
`{0, …, n-1}`. -/
def levelFiber (t : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ :=
  (transversalLists t n).image Encodable.encode

/-- Decode a fiber code back to its list (total, via a default). -/
def decodeList (x : ℕ) : List ℕ :=
  (Encodable.decode (α := List ℕ) x).getD []

@[simp]
theorem decodeList_encode (l : List ℕ) : decodeList (Encodable.encode l) = l := by
  simp [decodeList]

theorem decodeList_spec {t : ℕ → Finset ℕ} {n x : ℕ} (hx : x ∈ levelFiber t n) :
    decodeList x ∈ transversalLists t n ∧ Encodable.encode (decodeList x) = x := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
  simpa using hl

/-- Truncating an injective partial transversal stays one. -/
theorem take_mem_transversalLists {t : ℕ → Finset ℕ} {n : ℕ} {l : List ℕ}
    (hl : l ∈ transversalLists t (n + 1)) : l.take n ∈ transversalLists t n := by
  obtain ⟨⟨hlen, hmem⟩, hnd⟩ := mem_transversalLists.mp hl
  refine mem_transversalLists.mpr
    ⟨⟨by rw [List.length_take, hlen]; omega, fun i hi => ?_⟩, hnd.sublist (l.take_sublist n)⟩
  have hi' : i < n := by
    have := hi
    rw [List.length_take, hlen] at this
    omega
  rw [List.getElem_take]
  exact hmem i (by omega)

/-! ## Level nonemptiness from finite Hall

The one reuse of mathlib's Hall machinery: the *finite* marriage theorem
(`Finset.all_card_le_biUnion_card_iff_existsInjective'`) shows each level is nonempty. No
matching is selected: the witness list is produced directly from the finite Hall matching, and
nonemptiness of the `Finset` is a proposition. -/

theorem transversalLists_nonempty (t : ℕ → Finset ℕ)
    (ht : ∀ s : Finset ℕ, s.card ≤ (s.biUnion t).card) (n : ℕ) :
    (transversalLists t n).Nonempty := by
  have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion fun i => t i).card := by
    intro s
    have himg : (s.image Fin.val).biUnion t = s.biUnion fun i => t i :=
      Finset.image_biUnion
    calc s.card = (s.image Fin.val).card :=
          (Finset.card_image_of_injective s Fin.val_injective).symm
      _ ≤ ((s.image Fin.val).biUnion t).card := ht _
      _ = (s.biUnion fun i => t i).card := by rw [himg]
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' fun i : Fin n => t i).mp hall
  refine ⟨List.ofFn f, mem_transversalLists.mpr ⟨⟨by simp, fun i hi => ?_⟩, ?_⟩⟩
  · have hi' : i < n := by simpa using hi
    rw [List.getElem_ofFn]
    exact hfmem _
  · exact List.nodup_ofFn.mpr hfinj

/-! ## The inverse system and the relative theorem -/

/-- The Hall inverse system of `t`: level `n` is the explicitly finite set of codes of
injective partial transversals on `{0, …, n-1}`, restriction truncates, and finite Hall
supplies nonemptiness. -/
def hallSystem (t : ℕ → Finset ℕ) (ht : ∀ s : Finset ℕ, s.card ≤ (s.biUnion t).card) :
    ExplicitFiniteInverseSystem where
  fiber n := levelFiber t n
  restrict n x := ⟨Encodable.encode ((decodeList x.1).take n), by
    obtain ⟨hmem, -⟩ := decodeList_spec x.2
    exact Finset.mem_image.mpr ⟨_, take_mem_transversalLists hmem, rfl⟩⟩
  nonempty n := (transversalLists_nonempty t ht n).image Encodable.encode

/-- **Countable Hall from explicit finite inverse-limit compactness.** The compactness
principle is a hypothesis, never derived: this theorem is an ambient-Lean factorization whose
proof term uses finite Hall and coding only — certified by the dependency assertions in
`scripts/MetaSmoke.lean`, which check that neither mathlib's infinite Hall theorem, nor
`nonempty_sections_of_finite_inverse_system`, nor the `hallMatchingsOn`/`hallMatchingsFunctor`
selection scaffolding occurs in its proof-only closure. (The absence of a
`Classical.indefiniteDescription` *selection step* is an occurrence-level fact, visible in the
construction — fibers come with `Finset.Nonempty` proofs and nothing is ever extracted from a
`Nonempty` instance — but is not assertable at constant granularity, since `Classical.em`
itself reaches that constant.) -/
theorem countableHall_of_finiteInverseLimitCompactness
    (hcompact : ExplicitFiniteInverseLimitCompactness) : CountableHall := by
  intro t ht
  obtain ⟨s, hs, hcoh⟩ := hcompact (hallSystem t ht)
  set L : ℕ → List ℕ := fun n => decodeList (s n) with hL
  have hLmem : ∀ n, L n ∈ transversalLists t n := fun n => (decodeList_spec (hs n)).1
  have hLlen : ∀ n, (L n).length = n := fun n => (mem_transversalLists.mp (hLmem n)).1.1
  have hLtake : ∀ n, (L (n + 1)).take n = L n := by
    intro n
    have hcohn := hcoh n
    simp only [hallSystem] at hcohn
    have henc : Encodable.encode ((L (n + 1)).take n) = Encodable.encode (L n) := by
      rw [hL]
      simpa [decodeList_spec (hs n) |>.2] using hcohn
    exact Encodable.encode_injective henc
  -- entries of the chain are stable across levels
  have hLprefix : ∀ {n m : ℕ}, n ≤ m → (L m).take n = L n := by
    intro n m hnm
    induction m with
    | zero =>
      have : n = 0 := by omega
      subst this
      simp [List.take_of_length_le (by rw [hLlen])]
    | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h | h
      · have hnm' : n ≤ m := by omega
        rw [← ih hnm', ← hLtake m, List.take_take, Nat.min_eq_left hnm']
      · have : n = m + 1 := by omega
        subst this
        exact List.take_of_length_le (by rw [hLlen])
  have hget : ∀ {n m i : ℕ} (hnm : n ≤ m) (hi : i < n),
      (L m)[i]'(by rw [hLlen]; omega) = (L n)[i]'(by rw [hLlen]; omega) := by
    intro n m i hnm hi
    have hw : i < ((L m).take n).length := by
      rw [List.length_take, hLlen]
      omega
    calc (L m)[i]'(by rw [hLlen]; omega)
        = ((L m).take n)[i]'hw := (List.getElem_take (h := hw)).symm
      _ = (L n)[i]'(by rw [hLlen]; omega) := by
          have := List.getElem_of_eq (hLprefix hnm) hw
          simpa using this
  refine ⟨fun k => (L (k + 1))[k]'(by rw [hLlen]; omega), ?_, ?_⟩
  · intro j k hjk
    have hjk' : (L (j + 1))[j]'(by rw [hLlen]; omega) = (L (k + 1))[k]'(by rw [hLlen]; omega) :=
      hjk
    rcases Nat.lt_trichotomy j k with h | h | h
    · exfalso
      have hj : (L (k + 1))[j]'(by rw [hLlen]; omega) = (L (j + 1))[j]'(by rw [hLlen]; omega) :=
        hget (by omega) (by omega)
      have hnd : (L (k + 1)).Nodup := (mem_transversalLists.mp (hLmem (k + 1))).2
      have : j = k := hnd.getElem_inj_iff.mp (hj.trans hjk')
      omega
    · exact h
    · exfalso
      have hk : (L (j + 1))[k]'(by rw [hLlen]; omega) = (L (k + 1))[k]'(by rw [hLlen]; omega) :=
        hget (by omega) (by omega)
      have hnd : (L (j + 1)).Nodup := (mem_transversalLists.mp (hLmem (j + 1))).2
      have : j = k := hnd.getElem_inj_iff.mp (hjk'.trans hk.symm)
      omega
  · intro k
    exact (mem_transversalLists.mp (hLmem (k + 1))).1.2 k (by rw [hLlen]; omega)

end ReverseMathlib.Slice
