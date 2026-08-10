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

/-- The condition `f(i) = n`, as one graph query `Nat.pair i n ∈ F`. -/
def FHits (F : Set ℕ) (n i : ℕ) : Prop := Nat.pair i n ∈ F

/-- Neither injection hits `n` at index `i` — two finite queries, one negative
query to each graph: bounded and local, though not literally a single query. -/
def Neither (F G : Set ℕ) (n i : ℕ) : Prop := ¬FHits F n i ∧ ¬FHits G n i

open Classical in
/-- The shared three-way condition classifier at `(n, i)`: `0` = `f` hits, `1` =
`g`-only hits, `2` = neither — two finite queries, mirroring the rows' `f`-first
precedence mechanically so the reductions and coherence proofs split on one
value. -/
noncomputable def hitClass (F G : Set ℕ) (n i : ℕ) : ℕ :=
  if FHits F n i then 0 else if FHits G n i then 1 else 2

theorem hitClass_eq_zero_iff {F G : Set ℕ} {n i : ℕ} :
    hitClass F G n i = 0 ↔ FHits F n i := by
  classical
  simp only [hitClass]
  split_ifs <;> simp_all

theorem hitClass_eq_one_iff {F G : Set ℕ} {n i : ℕ} :
    hitClass F G n i = 1 ↔ FHits G n i ∧ ¬FHits F n i := by
  classical
  simp only [hitClass]
  split_ifs <;> simp_all

theorem hitClass_eq_two_iff {F G : Set ℕ} {n i : ℕ} :
    hitClass F G n i = 2 ↔ Neither F G n i := by
  classical
  simp only [hitClass, Neither]
  split_ifs <;> simp_all

theorem hitClass_lt_three (F G : Set ℕ) (n i : ℕ) : hitClass F G n i < 3 := by
  classical
  simp only [hitClass]
  split_ifs <;> omega

/-- The uniform three-case split every row proof uses. -/
theorem hitClass_cases (F G : Set ℕ) (n i : ℕ) :
    hitClass F G n i = 0 ∨ hitClass F G n i = 1 ∨ hitClass F G n i = 2 := by
  have := hitClass_lt_three F G n i
  omega

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
        if hitClass F G n i = 2 then yAt 0 n i else yChain 2 n i]
    else if j = 1 then
      [yChain 1 n i,
        if hitClass F G n i = 2 then yAt 1 n i else yChain 3 n i]
    else if j = 2 then
      [if i = 0 then yPlain n else yChain 2 n (i - 1),
        if hitClass F G n i = 2 then yChain 2 n i
          else if hitClass F G n i = 0 then yAt 0 n i else yAt 1 n i]
    else
      [if i = 0 then yPlain n else yChain 3 n (i - 1),
        if hitClass F G n i = 2 then yChain 3 n i
          else if hitClass F G n i = 0 then yAt 1 n i else yAt 0 n i]

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
        if hitClass F G n 0 = 2 then xChain 0 n 0
          else if hitClass F G n 0 = 0 then xChain 2 n 0 else xChain 3 n 0]
    else
      [xPlain n,
        if hitClass F G n 0 = 2 then xChain 1 n 0
          else if hitClass F G n 0 = 0 then xChain 3 n 0 else xChain 2 n 0]
  else
    let j := (yChainDecode v).1
    let n := (yChainDecode v).2.1
    let i0 := (yChainDecode v).2.2
    if j = 0 then
      [xChain 0 n i0,
        if hitClass F G n (i0 + 1) = 2 then xChain 0 n (i0 + 1)
          else if hitClass F G n (i0 + 1) = 0 then xChain 2 n (i0 + 1)
          else xChain 3 n (i0 + 1)]
    else if j = 1 then
      [xChain 1 n i0,
        if hitClass F G n (i0 + 1) = 2 then xChain 1 n (i0 + 1)
          else if hitClass F G n (i0 + 1) = 0 then xChain 3 n (i0 + 1)
          else xChain 2 n (i0 + 1)]
    else if j = 2 then
      [xChain 2 n (i0 + 1),
        if hitClass F G n i0 = 2 then xChain 2 n i0 else xChain 0 n i0]
    else
      [xChain 3 n (i0 + 1),
        if hitClass F G n i0 = 2 then xChain 3 n i0 else xChain 1 n i0]

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

/-! ### Row equations, per vertex family -/

private theorem xChain_mod2 (j n i : ℕ) : ¬xChain j n i % 2 = 0 := by
  simp only [xChain]
  omega

theorem ySpec_mod (b n : ℕ) :
    ¬ySpec b n % 2 = 0 ∧ ySpec b n % 4 = 1 := by
  simp only [ySpec]
  omega

theorem yChain_mod (j n i : ℕ) :
    ¬yChain j n i % 2 = 0 ∧ ¬yChain j n i % 4 = 1 := by
  simp only [yChain]
  omega

theorem leftRow_xPlain (F G : Set ℕ) (n : ℕ) :
    leftRow F G (xPlain n) = [ySpec 0 n, ySpec 1 n] := by
  have h2 : 2 * n % 2 = 0 := by omega
  have h3 : 2 * n / 2 = n := by omega
  simp only [leftRow, xPlain, if_pos h2, h3]

theorem leftRow_xChain (F G : Set ℕ) (j n i : ℕ) (hj : j < 4) :
    leftRow F G (xChain j n i) =
      if j = 0 then [yChain 0 n i,
        if hitClass F G n i = 2 then yAt 0 n i else yChain 2 n i]
      else if j = 1 then [yChain 1 n i,
        if hitClass F G n i = 2 then yAt 1 n i else yChain 3 n i]
      else if j = 2 then [if i = 0 then yPlain n else yChain 2 n (i - 1),
        if hitClass F G n i = 2 then yChain 2 n i
          else if hitClass F G n i = 0 then yAt 0 n i else yAt 1 n i]
      else [if i = 0 then yPlain n else yChain 3 n (i - 1),
        if hitClass F G n i = 2 then yChain 3 n i
          else if hitClass F G n i = 0 then yAt 1 n i else yAt 0 n i] := by
  classical
  simp only [leftRow, if_neg (xChain_mod2 j n i), xDecode_xChain hj]

theorem rightRow_yPlain (F G : Set ℕ) (n : ℕ) :
    rightRow F G (yPlain n) = [xChain 2 n 0, xChain 3 n 0] := by
  have h2 : 2 * n % 2 = 0 := by omega
  have h3 : 2 * n / 2 = n := by omega
  simp only [rightRow, yPlain, if_pos h2, h3]

theorem rightRow_ySpec (F G : Set ℕ) (b n : ℕ) (hb : b < 2) :
    rightRow F G (ySpec b n) =
      if b = 0 then [xPlain n,
        if hitClass F G n 0 = 2 then xChain 0 n 0
          else if hitClass F G n 0 = 0 then xChain 2 n 0 else xChain 3 n 0]
      else [xPlain n,
        if hitClass F G n 0 = 2 then xChain 1 n 0
          else if hitClass F G n 0 = 0 then xChain 3 n 0 else xChain 2 n 0] := by
  classical
  obtain ⟨hm2, hm4⟩ := ySpec_mod b n
  simp only [rightRow, if_neg hm2, if_pos hm4, ySpecDecode_ySpec hb]

theorem rightRow_yChain (F G : Set ℕ) (j n i0 : ℕ) (hj : j < 4) :
    rightRow F G (yChain j n i0) =
      if j = 0 then [xChain 0 n i0,
        if hitClass F G n (i0 + 1) = 2 then xChain 0 n (i0 + 1)
          else if hitClass F G n (i0 + 1) = 0 then xChain 2 n (i0 + 1)
          else xChain 3 n (i0 + 1)]
      else if j = 1 then [xChain 1 n i0,
        if hitClass F G n (i0 + 1) = 2 then xChain 1 n (i0 + 1)
          else if hitClass F G n (i0 + 1) = 0 then xChain 3 n (i0 + 1)
          else xChain 2 n (i0 + 1)]
      else if j = 2 then [xChain 2 n (i0 + 1),
        if hitClass F G n i0 = 2 then xChain 2 n i0 else xChain 0 n i0]
      else [xChain 3 n (i0 + 1),
        if hitClass F G n i0 = 2 then xChain 3 n i0 else xChain 1 n i0] := by
  classical
  obtain ⟨hm2, hm4⟩ := yChain_mod j n i0
  simp only [rightRow, if_neg hm2, if_neg hm4, yChainDecode_yChain hj]

/-! ### Row nodup: each row's two entries are distinct -/

private theorem nodup_pair {A B : ℕ} (hAB : A ≠ B) : List.Nodup [A, B] := by
  simp [List.nodup_cons, hAB]

theorem leftRow_nodup (F G : Set ℕ) (v : ℕ) : (leftRow F G v).Nodup := by
  classical
  rcases xCases v with ⟨n, rfl⟩ | ⟨j, n, i, hj, rfl⟩
  · rw [leftRow_xPlain]
    refine nodup_pair fun h => ?_
    obtain ⟨hb, -⟩ := ySpec_injective (by omega) (by omega) h
    omega
  · rw [leftRow_xChain F G j n i hj]
    have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases hj4 with rfl | rfl | rfl | rfl <;>
        simp only [reduceIte, yAt_zero] <;> split_ifs <;>
        refine nodup_pair fun h => ?_ <;>
        first
          | (exfalso; omega)
          | (obtain ⟨h1, -, h3⟩ := yChain_injective (by omega) (by omega) h; omega)
          | (exact ySpec_ne_yChain _ _ _ _ _ h.symm)
          | (exact yPlain_ne_yChain _ _ _ _ h)
          | (exact yPlain_ne_ySpec _ _ _ h)
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rcases hj4 with rfl | rfl | rfl | rfl <;>
        simp only [reduceIte, yAt_succ, Nat.add_sub_cancel] <;> split_ifs <;>
        refine nodup_pair fun h => ?_ <;>
        first
          | (exfalso; omega)
          | (obtain ⟨h1, -, h3⟩ := yChain_injective (by omega) (by omega) h; omega)

theorem rightRow_nodup (F G : Set ℕ) (v : ℕ) : (rightRow F G v).Nodup := by
  classical
  rcases yCases v with ⟨n, rfl⟩ | ⟨b, n, hb, rfl⟩ | ⟨j, n, i0, hj, rfl⟩
  · rw [rightRow_yPlain]
    refine nodup_pair fun h => ?_
    obtain ⟨h1, -, -⟩ := xChain_injective (by omega) (by omega) h
    omega
  · rw [rightRow_ySpec F G b n hb]
    have hb2 : b = 0 ∨ b = 1 := by omega
    rcases hb2 with rfl | rfl
    · rw [if_pos rfl]
      split_ifs <;> exact nodup_pair fun h => xPlain_ne_xChain _ _ _ _ h
    · rw [if_neg (by omega)]
      split_ifs <;> exact nodup_pair fun h => xPlain_ne_xChain _ _ _ _ h
  · rw [rightRow_yChain F G j n i0 hj]
    have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj4 with rfl | rfl | rfl | rfl
    · rw [if_pos rfl]
      split_ifs <;> refine nodup_pair fun h => ?_ <;>
        (obtain ⟨h1, -, h3⟩ := xChain_injective (by omega) (by omega) h; omega)
    · rw [if_neg (by omega), if_pos rfl]
      split_ifs <;> refine nodup_pair fun h => ?_ <;>
        (obtain ⟨h1, -, h3⟩ := xChain_injective (by omega) (by omega) h; omega)
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      split_ifs <;> refine nodup_pair fun h => ?_ <;>
        (obtain ⟨h1, -, h3⟩ := xChain_injective (by omega) (by omega) h; omega)
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      split_ifs <;> refine nodup_pair fun h => ?_ <;>
        (obtain ⟨h1, -, h3⟩ := xChain_injective (by omega) (by omega) h; omega)

/-! ### Positional introduction helpers for the eighteen edge families -/

namespace GadgetAdj

variable {F G : Set ℕ}

theorem d1 (n : ℕ) : GadgetAdj F G (xPlain n) (ySpec 0 n) :=
  Or.inl ⟨n, rfl, rfl⟩

theorem d2 (n : ℕ) : GadgetAdj F G (xPlain n) (ySpec 1 n) :=
  Or.inr (Or.inl ⟨n, rfl, rfl⟩)

theorem d3 (n : ℕ) : GadgetAdj F G (xChain 2 n 0) (yPlain n) :=
  Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))

theorem d4 (n : ℕ) : GadgetAdj F G (xChain 3 n 0) (yPlain n) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩)))

theorem d5 (n i : ℕ) : GadgetAdj F G (xChain 0 n i) (yChain 0 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl⟩))))

theorem d6 (n i : ℕ) : GadgetAdj F G (xChain 1 n i) (yChain 1 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl⟩)))))

theorem d7 (n i : ℕ) (hc : Neither F G n i) : GadgetAdj F G (xChain 0 n i) (yAt 0 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl, hc⟩))))))

theorem d8 (n i : ℕ) (hc : Neither F G n i) : GadgetAdj F G (xChain 1 n i) (yAt 1 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl, hc⟩)))))))

theorem d9 (n i : ℕ) : GadgetAdj F G (xChain 2 n (i + 1)) (yChain 2 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl⟩))))))))

theorem d10 (n i : ℕ) : GadgetAdj F G (xChain 3 n (i + 1)) (yChain 3 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl,
    rfl⟩)))))))))

theorem d11 (n i : ℕ) (hc : Neither F G n i) : GadgetAdj F G (xChain 2 n i) (yChain 2 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i,
    rfl, rfl, hc⟩))))))))))

theorem d12 (n i : ℕ) (hc : Neither F G n i) : GadgetAdj F G (xChain 3 n i) (yChain 3 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨n, i, rfl, rfl, hc⟩)))))))))))

theorem d13 (n i : ℕ) (hc : FHits F n i) : GadgetAdj F G (xChain 2 n i) (yAt 0 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨n, i, rfl, rfl, hc⟩))))))))))))

theorem d14 (n i : ℕ) (hc : FHits F n i) : GadgetAdj F G (xChain 3 n i) (yAt 1 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨n, i, rfl, rfl, hc⟩)))))))))))))

theorem d15 (n i : ℕ) (hc : FHits G n i) (hnc : ¬FHits F n i) :
    GadgetAdj F G (xChain 2 n i) (yAt 1 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl, hc, hnc⟩))))))))))))))

theorem d16 (n i : ℕ) (hc : FHits G n i) (hnc : ¬FHits F n i) :
    GadgetAdj F G (xChain 3 n i) (yAt 0 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl, hc, hnc⟩)))))))))))))))

theorem d17 (n i : ℕ) (hc : ¬Neither F G n i) : GadgetAdj F G (xChain 0 n i) (yChain 2 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, i, rfl, rfl, hc⟩))))))))))))))))

theorem d18 (n i : ℕ) (hc : ¬Neither F G n i) : GadgetAdj F G (xChain 1 n i) (yChain 3 n i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨n, i, rfl, rfl, hc⟩)))))))))))))))))

end GadgetAdj

/-! ### The edge relation through the rows -/

private theorem mem_pair' {a x y : ℕ} : a ∈ [x, y] ↔ a = x ∨ a = y := by
  simp

/-- **Adjacency through the left row** (review pin): `GadgetAdj` is exactly
membership in the finite two-entry left row, so adjacency decidability and the
edge-set reduction inherit the row computation — no search through the eighteen
disjuncts ever enters a reduction. -/
theorem gadgetAdj_iff_mem_leftRow (F G : Set ℕ) (a b : ℕ) :
    GadgetAdj F G a b ↔ b ∈ leftRow F G a := by
  classical
  constructor
  · rintro (⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ |
      ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl, hc⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc, hnc⟩ | ⟨n, i, rfl, rfl, hc, hnc⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc⟩)
    · rw [leftRow_xPlain]
      simp
    · rw [leftRow_xPlain]
      simp
    · rw [leftRow_xChain F G 2 n 0 (by omega)]
      simp
    · rw [leftRow_xChain F G 3 n 0 (by omega)]
      simp
    · rw [leftRow_xChain F G 0 n i (by omega)]
      simp
    · rw [leftRow_xChain F G 1 n i (by omega)]
      simp
    · rw [leftRow_xChain F G 0 n i (by omega)]
      simp only [show hitClass F G n i = 2 from hitClass_eq_two_iff.mpr hc, reduceIte]
      simp
    · rw [leftRow_xChain F G 1 n i (by omega)]
      simp only [show hitClass F G n i = 2 from hitClass_eq_two_iff.mpr hc, reduceIte]
      simp
    · rw [leftRow_xChain F G 2 n (i + 1) (by omega)]
      simp
    · rw [leftRow_xChain F G 3 n (i + 1) (by omega)]
      simp
    · rw [leftRow_xChain F G 2 n i (by omega)]
      simp only [show hitClass F G n i = 2 from hitClass_eq_two_iff.mpr hc, reduceIte]
      simp
    · rw [leftRow_xChain F G 3 n i (by omega)]
      simp only [show hitClass F G n i = 2 from hitClass_eq_two_iff.mpr hc, reduceIte]
      simp
    · rw [leftRow_xChain F G 2 n i (by omega)]
      simp only [show hitClass F G n i = 0 from hitClass_eq_zero_iff.mpr hc, reduceIte]
      simp
    · rw [leftRow_xChain F G 3 n i (by omega)]
      simp only [show hitClass F G n i = 0 from hitClass_eq_zero_iff.mpr hc, reduceIte]
      simp
    · rw [leftRow_xChain F G 2 n i (by omega)]
      simp only [show hitClass F G n i = 1 from hitClass_eq_one_iff.mpr ⟨hc, hnc⟩,
        reduceIte]
      simp
    · rw [leftRow_xChain F G 3 n i (by omega)]
      simp only [show hitClass F G n i = 1 from hitClass_eq_one_iff.mpr ⟨hc, hnc⟩]
      simp
    · rw [leftRow_xChain F G 0 n i (by omega)]
      rcases hitClass_cases F G n i with h | h | h
      · simp only [h, reduceIte]
        simp
      · simp only [h, reduceIte]
        simp
      · exact absurd (hitClass_eq_two_iff.mp h) hc
    · rw [leftRow_xChain F G 1 n i (by omega)]
      rcases hitClass_cases F G n i with h | h | h
      · simp only [h, reduceIte]
        simp
      · simp only [h, reduceIte]
        simp
      · exact absurd (hitClass_eq_two_iff.mp h) hc
  · intro hb
    rcases xCases a with ⟨n, rfl⟩ | ⟨j, n, i, hj, rfl⟩
    · rw [leftRow_xPlain] at hb
      rcases mem_pair'.mp hb with rfl | rfl
      · exact GadgetAdj.d1 n
      · exact GadgetAdj.d2 n
    · rw [leftRow_xChain F G j n i hj] at hb
      have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj4 with rfl | rfl | rfl | rfl
      · rw [if_pos (show (0:ℕ) = 0 from rfl)] at hb
        split_ifs at hb with h2
        · rcases mem_pair'.mp hb with rfl | rfl
          · exact GadgetAdj.d5 n i
          · exact GadgetAdj.d7 n i (hitClass_eq_two_iff.mp h2)
        · rcases mem_pair'.mp hb with rfl | rfl
          · exact GadgetAdj.d5 n i
          · exact GadgetAdj.d17 n i fun hN => h2 (hitClass_eq_two_iff.mpr hN)
      · rw [if_neg (show ¬(1:ℕ) = 0 by omega), if_pos (show (1:ℕ) = 1 from rfl)] at hb
        split_ifs at hb with h2
        · rcases mem_pair'.mp hb with rfl | rfl
          · exact GadgetAdj.d6 n i
          · exact GadgetAdj.d8 n i (hitClass_eq_two_iff.mp h2)
        · rcases mem_pair'.mp hb with rfl | rfl
          · exact GadgetAdj.d6 n i
          · exact GadgetAdj.d18 n i fun hN => h2 (hitClass_eq_two_iff.mpr hN)
      · rw [if_neg (show ¬(2:ℕ) = 0 by omega), if_neg (show ¬(2:ℕ) = 1 by omega),
          if_pos (show (2:ℕ) = 2 from rfl)] at hb
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [if_pos (show (0:ℕ) = 0 from rfl)] at hb
          split_ifs at hb with h2 h0
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d3 n
            · exact GadgetAdj.d11 n 0 (hitClass_eq_two_iff.mp h2)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d3 n
            · exact GadgetAdj.d13 n 0 (hitClass_eq_zero_iff.mp h0)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d3 n
            · have h1 : hitClass F G n 0 = 1 := by
                have := hitClass_lt_three F G n 0
                omega
              obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
              exact GadgetAdj.d15 n 0 hcG hncF
        · rw [if_neg (show ¬i = 0 by omega)] at hb
          obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          rw [Nat.add_sub_cancel] at hb
          split_ifs at hb with h2 h0
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d9 n k
            · exact GadgetAdj.d11 n (k + 1) (hitClass_eq_two_iff.mp h2)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d9 n k
            · exact GadgetAdj.d13 n (k + 1) (hitClass_eq_zero_iff.mp h0)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d9 n k
            · have h1 : hitClass F G n (k + 1) = 1 := by
                have := hitClass_lt_three F G n (k + 1)
                omega
              obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
              exact GadgetAdj.d15 n (k + 1) hcG hncF
      · rw [if_neg (show ¬(3:ℕ) = 0 by omega), if_neg (show ¬(3:ℕ) = 1 by omega),
          if_neg (show ¬(3:ℕ) = 2 by omega)] at hb
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [if_pos (show (0:ℕ) = 0 from rfl)] at hb
          split_ifs at hb with h2 h0
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d4 n
            · exact GadgetAdj.d12 n 0 (hitClass_eq_two_iff.mp h2)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d4 n
            · exact GadgetAdj.d14 n 0 (hitClass_eq_zero_iff.mp h0)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d4 n
            · have h1 : hitClass F G n 0 = 1 := by
                have := hitClass_lt_three F G n 0
                omega
              obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
              exact GadgetAdj.d16 n 0 hcG hncF
        · rw [if_neg (show ¬i = 0 by omega)] at hb
          obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          rw [Nat.add_sub_cancel] at hb
          split_ifs at hb with h2 h0
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d10 n k
            · exact GadgetAdj.d12 n (k + 1) (hitClass_eq_two_iff.mp h2)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d10 n k
            · exact GadgetAdj.d14 n (k + 1) (hitClass_eq_zero_iff.mp h0)
          · rcases mem_pair'.mp hb with rfl | rfl
            · exact GadgetAdj.d10 n k
            · have h1 : hitClass F G n (k + 1) = 1 := by
                have := hitClass_lt_three F G n (k + 1)
                omega
              obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
              exact GadgetAdj.d16 n (k + 1) hcG hncF

/-! ### The edge set, definitionally row-based -/

open Classical in
/-- The gadget's edge set, **definitionally row-based** (review pin): membership
IS the finite two-entry left-row computation, so "no existential search" is
visible in the construction itself, not merely recoverable from a proof
rewrite. `mem_gadgetEdges_iff` is its semantic characterization against the
eighteen-family relation. -/
noncomputable def gadgetEdges (F G : Set ℕ) : Set ℕ :=
  {p | p.unpair.2 ∈ leftRow F G p.unpair.1}

theorem mem_gadgetEdges_iff {F G : Set ℕ} {a b : ℕ} :
    Nat.pair a b ∈ gadgetEdges F G ↔ GadgetAdj F G a b := by
  classical
  simp only [gadgetEdges, Set.mem_setOf_eq, Nat.unpair_pair]
  exact (gadgetAdj_iff_mem_leftRow F G a b).symm

/-- **Adjacency through the right row**: the mirror characterization, which
establishes the two rows' coherence against the same row-defined edge set. -/
theorem gadgetAdj_iff_mem_rightRow (F G : Set ℕ) (a b : ℕ) :
    GadgetAdj F G a b ↔ a ∈ rightRow F G b := by
  classical
  constructor
  · rintro (⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ |
      ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl, hc⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc, hnc⟩ | ⟨n, i, rfl, rfl, hc, hnc⟩ |
      ⟨n, i, rfl, rfl, hc⟩ | ⟨n, i, rfl, rfl, hc⟩)
    · rw [rightRow_ySpec F G 0 n (by omega), if_pos (show (0:ℕ) = 0 from rfl)]
      simp
    · rw [rightRow_ySpec F G 1 n (by omega), if_neg (show ¬(1:ℕ) = 0 by omega)]
      simp
    · rw [rightRow_yPlain]
      simp
    · rw [rightRow_yPlain]
      simp
    · rw [rightRow_yChain F G 0 n i (by omega), if_pos (show (0:ℕ) = 0 from rfl)]
      simp
    · rw [rightRow_yChain F G 1 n i (by omega),
        if_neg (show ¬(1:ℕ) = 0 by omega), if_pos (show (1:ℕ) = 1 from rfl)]
      simp
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [yAt_zero, rightRow_ySpec F G 0 n (by omega),
          if_pos (show (0:ℕ) = 0 from rfl)]
        simp only [show hitClass F G n 0 = 2 from hitClass_eq_two_iff.mpr hc,
          reduceIte]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [yAt_succ, rightRow_yChain F G 0 n k (by omega),
          if_pos (show (0:ℕ) = 0 from rfl)]
        simp only [show hitClass F G n (k + 1) = 2 from hitClass_eq_two_iff.mpr hc,
          reduceIte]
        simp
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [yAt_zero, rightRow_ySpec F G 1 n (by omega),
          if_neg (show ¬(1:ℕ) = 0 by omega)]
        simp only [show hitClass F G n 0 = 2 from hitClass_eq_two_iff.mpr hc,
          reduceIte]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [yAt_succ, rightRow_yChain F G 1 n k (by omega),
          if_neg (show ¬(1:ℕ) = 0 by omega), if_pos (show (1:ℕ) = 1 from rfl)]
        simp only [show hitClass F G n (k + 1) = 2 from hitClass_eq_two_iff.mpr hc,
          reduceIte]
        simp
    · rw [rightRow_yChain F G 2 n i (by omega),
        if_neg (show ¬(2:ℕ) = 0 by omega), if_neg (show ¬(2:ℕ) = 1 by omega),
        if_pos (show (2:ℕ) = 2 from rfl)]
      simp
    · rw [rightRow_yChain F G 3 n i (by omega),
        if_neg (show ¬(3:ℕ) = 0 by omega), if_neg (show ¬(3:ℕ) = 1 by omega),
        if_neg (show ¬(3:ℕ) = 2 by omega)]
      simp
    · rw [rightRow_yChain F G 2 n i (by omega),
        if_neg (show ¬(2:ℕ) = 0 by omega), if_neg (show ¬(2:ℕ) = 1 by omega),
        if_pos (show (2:ℕ) = 2 from rfl)]
      simp only [show hitClass F G n i = 2 from hitClass_eq_two_iff.mpr hc,
        reduceIte]
      simp
    · rw [rightRow_yChain F G 3 n i (by omega),
        if_neg (show ¬(3:ℕ) = 0 by omega), if_neg (show ¬(3:ℕ) = 1 by omega),
        if_neg (show ¬(3:ℕ) = 2 by omega)]
      simp only [show hitClass F G n i = 2 from hitClass_eq_two_iff.mpr hc,
        reduceIte]
      simp
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [yAt_zero, rightRow_ySpec F G 0 n (by omega),
          if_pos (show (0:ℕ) = 0 from rfl)]
        simp only [show hitClass F G n 0 = 0 from hitClass_eq_zero_iff.mpr hc,
          reduceIte]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [yAt_succ, rightRow_yChain F G 0 n k (by omega),
          if_pos (show (0:ℕ) = 0 from rfl)]
        simp only [show hitClass F G n (k + 1) = 0 from hitClass_eq_zero_iff.mpr hc,
          reduceIte]
        simp
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [yAt_zero, rightRow_ySpec F G 1 n (by omega),
          if_neg (show ¬(1:ℕ) = 0 by omega)]
        simp only [show hitClass F G n 0 = 0 from hitClass_eq_zero_iff.mpr hc,
          reduceIte]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [yAt_succ, rightRow_yChain F G 1 n k (by omega),
          if_neg (show ¬(1:ℕ) = 0 by omega), if_pos (show (1:ℕ) = 1 from rfl)]
        simp only [show hitClass F G n (k + 1) = 0 from hitClass_eq_zero_iff.mpr hc,
          reduceIte]
        simp
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [yAt_zero, rightRow_ySpec F G 1 n (by omega),
          if_neg (show ¬(1:ℕ) = 0 by omega)]
        simp only [show hitClass F G n 0 = 1 from hitClass_eq_one_iff.mpr ⟨hc, hnc⟩]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [yAt_succ, rightRow_yChain F G 1 n k (by omega),
          if_neg (show ¬(1:ℕ) = 0 by omega), if_pos (show (1:ℕ) = 1 from rfl)]
        simp only [show hitClass F G n (k + 1) = 1 from
          hitClass_eq_one_iff.mpr ⟨hc, hnc⟩]
        simp
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [yAt_zero, rightRow_ySpec F G 0 n (by omega),
          if_pos (show (0:ℕ) = 0 from rfl)]
        simp only [show hitClass F G n 0 = 1 from hitClass_eq_one_iff.mpr ⟨hc, hnc⟩]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [yAt_succ, rightRow_yChain F G 0 n k (by omega),
          if_pos (show (0:ℕ) = 0 from rfl)]
        simp only [show hitClass F G n (k + 1) = 1 from
          hitClass_eq_one_iff.mpr ⟨hc, hnc⟩]
        simp
    · rw [rightRow_yChain F G 2 n i (by omega),
        if_neg (show ¬(2:ℕ) = 0 by omega), if_neg (show ¬(2:ℕ) = 1 by omega),
        if_pos (show (2:ℕ) = 2 from rfl)]
      rcases hitClass_cases F G n i with h | h | h
      · simp only [h]
        simp
      · simp only [h]
        simp
      · exact absurd (hitClass_eq_two_iff.mp h) hc
    · rw [rightRow_yChain F G 3 n i (by omega),
        if_neg (show ¬(3:ℕ) = 0 by omega), if_neg (show ¬(3:ℕ) = 1 by omega),
        if_neg (show ¬(3:ℕ) = 2 by omega)]
      rcases hitClass_cases F G n i with h | h | h
      · simp only [h]
        simp
      · simp only [h]
        simp
      · exact absurd (hitClass_eq_two_iff.mp h) hc
  · intro ha
    rcases yCases b with ⟨n, rfl⟩ | ⟨c, n, hc2, rfl⟩ | ⟨j, n, i0, hj, rfl⟩
    · rw [rightRow_yPlain] at ha
      rcases mem_pair'.mp ha with rfl | rfl
      · exact GadgetAdj.d3 n
      · exact GadgetAdj.d4 n
    · rw [rightRow_ySpec F G c n hc2] at ha
      have hc02 : c = 0 ∨ c = 1 := by omega
      rcases hc02 with rfl | rfl
      · rw [if_pos (show (0:ℕ) = 0 from rfl)] at ha
        split_ifs at ha with h2 h0
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d1 n
          · have := GadgetAdj.d7 (F := F) (G := G) n 0
              (hitClass_eq_two_iff.mp h2)
            rwa [yAt_zero] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d1 n
          · have := GadgetAdj.d13 (F := F) (G := G) n 0
              (hitClass_eq_zero_iff.mp h0)
            rwa [yAt_zero] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d1 n
          · have h1 : hitClass F G n 0 = 1 := by
              have := hitClass_lt_three F G n 0
              omega
            obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
            have := GadgetAdj.d16 (F := F) (G := G) n 0 hcG hncF
            rwa [yAt_zero] at this
      · rw [if_neg (show ¬(1:ℕ) = 0 by omega)] at ha
        split_ifs at ha with h2 h0
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d2 n
          · have := GadgetAdj.d8 (F := F) (G := G) n 0
              (hitClass_eq_two_iff.mp h2)
            rwa [yAt_zero] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d2 n
          · have := GadgetAdj.d14 (F := F) (G := G) n 0
              (hitClass_eq_zero_iff.mp h0)
            rwa [yAt_zero] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d2 n
          · have h1 : hitClass F G n 0 = 1 := by
              have := hitClass_lt_three F G n 0
              omega
            obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
            have := GadgetAdj.d15 (F := F) (G := G) n 0 hcG hncF
            rwa [yAt_zero] at this
    · rw [rightRow_yChain F G j n i0 hj] at ha
      have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj4 with rfl | rfl | rfl | rfl
      · rw [if_pos (show (0:ℕ) = 0 from rfl)] at ha
        split_ifs at ha with h2 h0
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d5 n i0
          · have := GadgetAdj.d7 (F := F) (G := G) n (i0 + 1)
              (hitClass_eq_two_iff.mp h2)
            rwa [yAt_succ] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d5 n i0
          · have := GadgetAdj.d13 (F := F) (G := G) n (i0 + 1)
              (hitClass_eq_zero_iff.mp h0)
            rwa [yAt_succ] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d5 n i0
          · have h1 : hitClass F G n (i0 + 1) = 1 := by
              have := hitClass_lt_three F G n (i0 + 1)
              omega
            obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
            have := GadgetAdj.d16 (F := F) (G := G) n (i0 + 1) hcG hncF
            rwa [yAt_succ] at this
      · rw [if_neg (show ¬(1:ℕ) = 0 by omega),
          if_pos (show (1:ℕ) = 1 from rfl)] at ha
        split_ifs at ha with h2 h0
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d6 n i0
          · have := GadgetAdj.d8 (F := F) (G := G) n (i0 + 1)
              (hitClass_eq_two_iff.mp h2)
            rwa [yAt_succ] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d6 n i0
          · have := GadgetAdj.d14 (F := F) (G := G) n (i0 + 1)
              (hitClass_eq_zero_iff.mp h0)
            rwa [yAt_succ] at this
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d6 n i0
          · have h1 : hitClass F G n (i0 + 1) = 1 := by
              have := hitClass_lt_three F G n (i0 + 1)
              omega
            obtain ⟨hcG, hncF⟩ := hitClass_eq_one_iff.mp h1
            have := GadgetAdj.d15 (F := F) (G := G) n (i0 + 1) hcG hncF
            rwa [yAt_succ] at this
      · rw [if_neg (show ¬(2:ℕ) = 0 by omega), if_neg (show ¬(2:ℕ) = 1 by omega),
          if_pos (show (2:ℕ) = 2 from rfl)] at ha
        split_ifs at ha with h2
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d9 n i0
          · exact GadgetAdj.d11 n i0 (hitClass_eq_two_iff.mp h2)
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d9 n i0
          · exact GadgetAdj.d17 n i0 fun hN => h2 (hitClass_eq_two_iff.mpr hN)
      · rw [if_neg (show ¬(3:ℕ) = 0 by omega), if_neg (show ¬(3:ℕ) = 1 by omega),
          if_neg (show ¬(3:ℕ) = 2 by omega)] at ha
        split_ifs at ha with h2
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d10 n i0
          · exact GadgetAdj.d12 n i0 (hitClass_eq_two_iff.mp h2)
        · rcases mem_pair'.mp ha with rfl | rfl
          · exact GadgetAdj.d10 n i0
          · exact GadgetAdj.d18 n i0 fun hN => h2 (hitClass_eq_two_iff.mpr hN)

/-- The two rows cohere against the same row-defined edge set. -/
theorem mem_rightRow_iff_mem_gadgetEdges {F G : Set ℕ} {a b : ℕ} :
    a ∈ rightRow F G b ↔ Nat.pair a b ∈ gadgetEdges F G := by
  rw [mem_gadgetEdges_iff]
  exact (gadgetAdj_iff_mem_rightRow F G a b).symm

end SeparationGadget

end ReverseMathlib.Omega
