/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.RangeSeparation
import ReverseMathlib.Omega.Bigraph

/-!
# The 2-regular separation gadget: vertex coding (issue #42, slice 4)

Source: Shafer (thesis), §6.1, proof of Theorem 6.1.2 (v) ⇒ (i), text
pp. 156–158 — the 2-regular bipartite graph built from two injections with
disjoint ranges, any perfect matching of which computes a separating set. This
module lays down the **vertex coding**: the source's vertex families

* left: `xₙ` and `xʲₙ,ᵢ` (`j < 4`),
* right: `yₙ`, `y⁰ₙ,₀`, `y¹ₙ,₀`, and `yʲₙ,ᵢ` (`i ≥ 1`, `j < 4`),

coded bijectively onto ℕ on each side, so the gadget is a genuine
`InternalTwoRegularBigraph` instance with total neighbor enumerators and no junk
vertices. The residue classes discriminate the families: even codes are the
plain vertices on both sides; odd left codes carry `(j, n, i)`; odd right codes
split mod 4 between the two `i = 0` specials and the `i ≥ 1` chain vertices.

Everything here is pure coding — the two injections enter only in the later row
construction, and then only through single graph queries. Provenance stays
**claimed-level**: the construction follows the cited source, and nothing here
upgrades that citation beyond a proof-carrying transcription.
-/

namespace ReverseMathlib.Omega

namespace SeparationGadget

/-! ### Left vertex codes -/

/-- The source's `xₙ`. -/
def xPlain (n : ℕ) : ℕ := 2 * n

/-- The source's `xʲₙ,ᵢ` (`j < 4`). -/
def xChain (j n i : ℕ) : ℕ := 8 * Nat.pair n i + 2 * j + 1

/-! ### Right vertex codes -/

/-- The source's `yₙ`. -/
def yPlain (n : ℕ) : ℕ := 2 * n

/-- The source's `yᵇₙ,₀` (`b < 2`) — the two `i = 0` specials. -/
def ySpec (b n : ℕ) : ℕ := 8 * n + 4 * b + 1

/-- The source's `yʲₙ,ᵢ₊₁` (`j < 4`) — the chain vertices, at `i ≥ 1` in source
indexing (the last argument here is `i`, coding source index `i + 1`). -/
def yChain (j n i : ℕ) : ℕ := 16 * Nat.pair n i + 4 * j + 3

/-! ### Family discrimination -/

theorem xPlain_ne_xChain (n j n' i' : ℕ) : xPlain n ≠ xChain j n' i' := by
  simp only [xPlain, xChain]
  omega

theorem xPlain_injective {n n' : ℕ} (h : xPlain n = xPlain n') : n = n' := by
  simp only [xPlain] at h
  omega

theorem xChain_injective {j n i j' n' i' : ℕ} (hj : j < 4) (hj' : j' < 4)
    (h : xChain j n i = xChain j' n' i') : j = j' ∧ n = n' ∧ i = i' := by
  simp only [xChain] at h
  have hp : Nat.pair n i = Nat.pair n' i' ∧ j = j' := by omega
  obtain ⟨hnn, hii⟩ := Nat.pair_eq_pair.mp hp.1
  exact ⟨hp.2, hnn, hii⟩

theorem yPlain_ne_ySpec (n b n' : ℕ) : yPlain n ≠ ySpec b n' := by
  simp only [yPlain, ySpec]
  omega

theorem yPlain_ne_yChain (n j n' i' : ℕ) : yPlain n ≠ yChain j n' i' := by
  simp only [yPlain, yChain]
  omega

theorem ySpec_ne_yChain (b n j n' i' : ℕ) :
    ySpec b n ≠ yChain j n' i' := by
  simp only [ySpec, yChain]
  omega

theorem yPlain_injective {n n' : ℕ} (h : yPlain n = yPlain n') : n = n' := by
  simp only [yPlain] at h
  omega

theorem ySpec_injective {b n b' n' : ℕ} (hb : b < 2) (hb' : b' < 2)
    (h : ySpec b n = ySpec b' n') : b = b' ∧ n = n' := by
  simp only [ySpec] at h
  omega

theorem yChain_injective {j n i j' n' i' : ℕ} (hj : j < 4) (hj' : j' < 4)
    (h : yChain j n i = yChain j' n' i') : j = j' ∧ n = n' ∧ i = i' := by
  simp only [yChain] at h
  have hp : Nat.pair n i = Nat.pair n' i' ∧ j = j' := by omega
  obtain ⟨hnn, hii⟩ := Nat.pair_eq_pair.mp hp.1
  exact ⟨hp.2, hnn, hii⟩

/-! ### Coverage: the codings are onto ℕ on each side

Together with the discrimination and injectivity lemmas above, these make "no
junk vertices" a **checked** property: the row enumerators eliminate through
`xCases`/`yCases`, never through modular-arithmetic inference at the use site. -/

/-- **Left coverage**: every natural is a left vertex code, in exactly one
family (exclusivity is `xPlain_ne_xChain`; witness uniqueness is
`xPlain_injective` / `xChain_injective`). -/
theorem xCases (v : ℕ) : (∃ n, v = xPlain n) ∨ ∃ j n i, j < 4 ∧ v = xChain j n i := by
  rcases Nat.even_or_odd v with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl ⟨m, by simp [xPlain]; omega⟩
  · refine Or.inr ⟨m % 4, (Nat.unpair (m / 4)).1, (Nat.unpair (m / 4)).2, by omega, ?_⟩
    have hpair : Nat.pair (Nat.unpair (m / 4)).1 (Nat.unpair (m / 4)).2 = m / 4 :=
      Nat.pair_unpair (m / 4)
    simp only [xChain, hpair]
    omega

/-- **Right coverage**: every natural is a right vertex code, in exactly one
family (exclusivity is the `_ne_` lemmas; witness uniqueness is the injectivity
lemmas). -/
theorem yCases (v : ℕ) : (∃ n, v = yPlain n) ∨
    (∃ b n, b < 2 ∧ v = ySpec b n) ∨ ∃ j n i, j < 4 ∧ v = yChain j n i := by
  rcases Nat.even_or_odd v with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl ⟨m, by simp [yPlain]; omega⟩
  · by_cases h4 : v % 4 = 1
    · refine Or.inr (Or.inl ⟨(v / 4) % 2, (v / 4) / 2, by omega, ?_⟩)
      simp only [ySpec]
      omega
    · have h4' : v % 4 = 3 := by omega
      refine Or.inr (Or.inr ⟨(v / 4) % 4, (Nat.unpair ((v / 4) / 4)).1,
        (Nat.unpair ((v / 4) / 4)).2, by omega, ?_⟩)
      have hpair : Nat.pair (Nat.unpair ((v / 4) / 4)).1
          (Nat.unpair ((v / 4) / 4)).2 = (v / 4) / 4 := Nat.pair_unpair ((v / 4) / 4)
      simp only [yChain, hpair]
      omega

/-! ### Round-trip decoders -/

/-- Decode an odd left code to its `(j, n, i)`. -/
def xDecode (v : ℕ) : ℕ × ℕ × ℕ :=
  ((v / 2) % 4, (Nat.unpair ((v / 2) / 4)).1, (Nat.unpair ((v / 2) / 4)).2)

theorem xDecode_xChain {j n i : ℕ} (hj : j < 4) :
    xDecode (xChain j n i) = (j, n, i) := by
  simp only [xDecode, xChain]
  have h1 : (8 * Nat.pair n i + 2 * j + 1) / 2 = 4 * Nat.pair n i + j := by omega
  rw [h1]
  have h2 : (4 * Nat.pair n i + j) % 4 = j := by omega
  have h3 : (4 * Nat.pair n i + j) / 4 = Nat.pair n i := by omega
  rw [h2, h3, Nat.unpair_pair]

/-- Decode a `≡ 1 (mod 4)` right code to its `(b, n)`. -/
def ySpecDecode (v : ℕ) : ℕ × ℕ := ((v / 4) % 2, (v / 4) / 2)

theorem ySpecDecode_ySpec {b n : ℕ} (hb : b < 2) :
    ySpecDecode (ySpec b n) = (b, n) := by
  simp only [ySpecDecode, ySpec, Prod.mk.injEq]
  constructor <;> omega

/-- Decode a `≡ 3 (mod 4)` right code to its `(j, n, i)`. -/
def yChainDecode (v : ℕ) : ℕ × ℕ × ℕ :=
  ((v / 4) % 4, (Nat.unpair ((v / 4) / 4)).1, (Nat.unpair ((v / 4) / 4)).2)

theorem yChainDecode_yChain {j n i : ℕ} (hj : j < 4) :
    yChainDecode (yChain j n i) = (j, n, i) := by
  simp only [yChainDecode, yChain]
  have h1 : (16 * Nat.pair n i + 4 * j + 3) / 4 = 4 * Nat.pair n i + j := by omega
  rw [h1]
  have h2 : (4 * Nat.pair n i + j) % 4 = j := by omega
  have h3 : (4 * Nat.pair n i + j) / 4 = Nat.pair n i := by omega
  rw [h2, h3, Nat.unpair_pair]

/-- The source's `yʲₙ,ᵢ` for arbitrary `i` in **source indexing**. DOMAIN
DISCIPLINE: the source defines this only for `j < 2` (any `i`) or `i ≥ 1` (any
`j < 4`) — an out-of-domain call like `yAt 2 n 0` would ALIAS a valid special
code (`ySpec 2 n = ySpec 0 (n + 1)`), so every use site must satisfy
`j < 2 ∨ 1 ≤ i`, and `yAt_injective` carries that hypothesis explicitly. -/
def yAt (j n i : ℕ) : ℕ :=
  if i = 0 then ySpec j n else yChain j n (i - 1)

theorem yAt_zero (j n : ℕ) : yAt j n 0 = ySpec j n := rfl

theorem yAt_succ (j n i : ℕ) : yAt j n (i + 1) = yChain j n i := by
  simp [yAt]

/-- Injectivity of `yAt` **on the source domain** — the checked form of the
domain discipline. -/
theorem yAt_injective {j n i j' n' i' : ℕ} (hd : j < 2 ∨ 1 ≤ i)
    (hd' : j' < 2 ∨ 1 ≤ i') (hj : j < 4) (hj' : j' < 4)
    (h : yAt j n i = yAt j' n' i') : j = j' ∧ n = n' ∧ i = i' := by
  rcases Nat.eq_zero_or_pos i with rfl | hi <;>
    rcases Nat.eq_zero_or_pos i' with rfl | hi'
  · rw [yAt_zero, yAt_zero] at h
    obtain ⟨hb, hn⟩ := ySpec_injective (by omega) (by omega) h
    exact ⟨hb, hn, rfl⟩
  · rw [yAt_zero] at h
    rw [show i' = (i' - 1) + 1 by omega, yAt_succ] at h
    exact absurd h (ySpec_ne_yChain _ _ _ _ _)
  · rw [yAt_zero] at h
    rw [show i = (i - 1) + 1 by omega, yAt_succ] at h
    exact absurd h.symm (ySpec_ne_yChain _ _ _ _ _)
  · rw [show i = (i - 1) + 1 by omega, yAt_succ] at h
    rw [show i' = (i' - 1) + 1 by omega, yAt_succ] at h
    obtain ⟨hjj, hnn, hii⟩ := yChain_injective hj hj' h
    exact ⟨hjj, hnn, by omega⟩

/-! ### The edge relation and the executable rows

`GadgetAdj` is the **one** edge relation — the source's `E`, one disjunct per
edge family, with `f`-precedence added to the two overlap-sensitive families so
structural coherence holds without assuming disjointness (under disjoint ranges
the precedence is vacuous, matching the source exactly). The executable rows
branch on parity/residue and the round-trip decoders only — the coverage
theorems are for proofs, never for computing row data. -/

/-- The condition `f(i) = n`, as the single graph query `Nat.pair i n ∈ F`. -/
def FHits (F : Set ℕ) (n i : ℕ) : Prop := Nat.pair i n ∈ F

/-- Neither injection hits `n` at index `i`. -/
def Neither (F G : Set ℕ) (n i : ℕ) : Prop := ¬FHits F n i ∧ ¬FHits G n i

/-- The source's edge set `E` (Shafer, text pp. 156–157), one disjunct per edge
family, on coded vertices. -/
def GadgetAdj (F G : Set ℕ) (a b : ℕ) : Prop :=
  (∃ n, a = xPlain n ∧ b = ySpec 0 n) ∨
  (∃ n, a = xPlain n ∧ b = ySpec 1 n) ∨
  (∃ n, a = xChain 2 n 0 ∧ b = yPlain n) ∨
  (∃ n, a = xChain 3 n 0 ∧ b = yPlain n) ∨
  (∃ n i, a = xChain 0 n i ∧ b = yChain 0 n i) ∨
  (∃ n i, a = xChain 1 n i ∧ b = yChain 1 n i) ∨
  (∃ n i, a = xChain 0 n i ∧ b = yAt 0 n i ∧ Neither F G n i) ∨
  (∃ n i, a = xChain 1 n i ∧ b = yAt 1 n i ∧ Neither F G n i) ∨
  (∃ n i, a = xChain 2 n (i + 1) ∧ b = yChain 2 n i) ∨
  (∃ n i, a = xChain 3 n (i + 1) ∧ b = yChain 3 n i) ∨
  (∃ n i, a = xChain 2 n i ∧ b = yChain 2 n i ∧ Neither F G n i) ∨
  (∃ n i, a = xChain 3 n i ∧ b = yChain 3 n i ∧ Neither F G n i) ∨
  (∃ n i, a = xChain 2 n i ∧ b = yAt 0 n i ∧ FHits F n i) ∨
  (∃ n i, a = xChain 3 n i ∧ b = yAt 1 n i ∧ FHits F n i) ∨
  (∃ n i, a = xChain 2 n i ∧ b = yAt 1 n i ∧ FHits G n i ∧ ¬FHits F n i) ∨
  (∃ n i, a = xChain 3 n i ∧ b = yAt 0 n i ∧ FHits G n i ∧ ¬FHits F n i) ∨
  (∃ n i, a = xChain 0 n i ∧ b = yChain 2 n i ∧ ¬Neither F G n i) ∨
  (∃ n i, a = xChain 1 n i ∧ b = yChain 3 n i ∧ ¬Neither F G n i)

open Classical in
/-- The left neighbor row: the two right-neighbors of left code `v`, per the
source's adjacency bullets, branching on parity and `xDecode` only. Classical
`decide` on the two condition queries is deliberate — layer-2 computability
relative to the two graphs is a separate theorem. -/
noncomputable def leftRow (F G : Set ℕ) (v : ℕ) : List ℕ :=
  if v % 2 = 0 then
    [ySpec 0 (v / 2), ySpec 1 (v / 2)]
  else
    let j := (xDecode v).1
    let n := (xDecode v).2.1
    let i := (xDecode v).2.2
    if j = 0 then
      [yChain 0 n i,
        if Neither F G n i then yAt 0 n i else yChain 2 n i]
    else if j = 1 then
      [yChain 1 n i,
        if Neither F G n i then yAt 1 n i else yChain 3 n i]
    else if j = 2 then
      [if i = 0 then yPlain n else yChain 2 n (i - 1),
        if Neither F G n i then yChain 2 n i
          else if FHits F n i then yAt 0 n i else yAt 1 n i]
    else
      [if i = 0 then yPlain n else yChain 3 n (i - 1),
        if Neither F G n i then yChain 3 n i
          else if FHits F n i then yAt 1 n i else yAt 0 n i]

open Classical in
/-- The right neighbor row: the two left-neighbors of right code `v`, branching
on parity/residue and the decoders only. For a chain vertex `yʲₙ,ᵢ₀₊₁` the
source's `j ∈ {0,1}` bullets condition at index `i₀ + 1` and the `j ∈ {2,3}`
bullets at index `i₀`. -/
noncomputable def rightRow (F G : Set ℕ) (v : ℕ) : List ℕ :=
  if v % 2 = 0 then
    [xChain 2 (v / 2) 0, xChain 3 (v / 2) 0]
  else if v % 4 = 1 then
    let b := (ySpecDecode v).1
    let n := (ySpecDecode v).2
    if b = 0 then
      [xPlain n,
        if Neither F G n 0 then xChain 0 n 0
          else if FHits F n 0 then xChain 2 n 0 else xChain 3 n 0]
    else
      [xPlain n,
        if Neither F G n 0 then xChain 1 n 0
          else if FHits F n 0 then xChain 3 n 0 else xChain 2 n 0]
  else
    let j := (yChainDecode v).1
    let n := (yChainDecode v).2.1
    let i0 := (yChainDecode v).2.2
    if j = 0 then
      [xChain 0 n i0,
        if Neither F G n (i0 + 1) then xChain 0 n (i0 + 1)
          else if FHits F n (i0 + 1) then xChain 2 n (i0 + 1)
          else xChain 3 n (i0 + 1)]
    else if j = 1 then
      [xChain 1 n i0,
        if Neither F G n (i0 + 1) then xChain 1 n (i0 + 1)
          else if FHits F n (i0 + 1) then xChain 3 n (i0 + 1)
          else xChain 2 n (i0 + 1)]
    else if j = 2 then
      [xChain 2 n (i0 + 1),
        if Neither F G n i0 then xChain 2 n i0 else xChain 0 n i0]
    else
      [xChain 3 n (i0 + 1),
        if Neither F G n i0 then xChain 3 n i0 else xChain 1 n i0]

@[simp]
theorem leftRow_length (F G : Set ℕ) (v : ℕ) : (leftRow F G v).length = 2 := by
  classical
  simp only [leftRow, apply_ite List.length, List.length_cons, List.length_nil,
    ite_self]

@[simp]
theorem rightRow_length (F G : Set ℕ) (v : ℕ) : (rightRow F G v).length = 2 := by
  classical
  simp only [rightRow, apply_ite List.length, List.length_cons, List.length_nil,
    ite_self]

end SeparationGadget

end ReverseMathlib.Omega
