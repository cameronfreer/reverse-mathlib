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

/-- The source's `yʲₙ,ᵢ` for arbitrary `i` in **source indexing**, defined where
the source defines it (`j < 2`, any `i`; or any `j < 4`, `i ≥ 1`): the `i = 0`
values are the specials, and `i ≥ 1` values are chain codes at shifted index. -/
def yAt (j n i : ℕ) : ℕ :=
  if i = 0 then ySpec j n else yChain j n (i - 1)

theorem yAt_zero (j n : ℕ) : yAt j n 0 = ySpec j n := rfl

theorem yAt_succ (j n i : ℕ) : yAt j n (i + 1) = yChain j n i := by
  simp [yAt]

end SeparationGadget

end ReverseMathlib.Omega
