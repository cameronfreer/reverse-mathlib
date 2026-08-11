/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.TreeSeparationCompile

/-!
# `separationToPath`: the decoder and the direction (issue #42, slice 5)

The decoder of the `separation → WKL` direction: the path read off a separating
set for the compiled injections. `prefixCode` grows the path one bit per step by
querying the separator **at the current node's fixed tag** `3 · σ` — never
searching either injection's range and never discovering an event stage; one
query per step is an audited property of this implementation, not something
expressed by the reducibility statement itself. The raw definition and the
reduction `pathSet_le_sep` mention **only** the separator (fine-dependency gate
in `scripts/MetaSmoke.lean`); the tree, the injections, injectivity,
disjointness, and `SeparatesRanges` enter only in path correctness, and the
path's internality proof uses only the separator's membership.

Correctness maintains the invariant *the current prefix has canonical
extensions at every later level*: choosing a dying child would force the
corresponding first-stage event (survivor determinacy plus monotone deadness
rule out the wrong side), putting the node's tag in the wrong injection's range
and contradicting the separator bit.
-/

namespace ReverseMathlib.Omega

namespace TreeSeparation

/-! ### The decoder -/

open Classical in
/-- The path prefix codes: one separator query per step, at the current node's
tag. -/
noncomputable def prefixCode (Z : Set ℕ) : ℕ → ℕ
  | 0 => seqCode []
  | i + 1 => seqCode (decodeSeq (prefixCode Z i) ++
      [if 3 * prefixCode Z i ∈ Z then 1 else 0])

/-- Layer 1 (raw, the specification): the decoded path — the set of bit-`1`
positions of the growing prefix. Mentions **only** the separator. -/
noncomputable def pathSet (Z : Set ℕ) : Set ℕ :=
  {i | (decodeSeq (prefixCode Z (i + 1))).getD i 0 = 1}

@[simp]
theorem prefixCode_length (Z : Set ℕ) (n : ℕ) :
    (decodeSeq (prefixCode Z n)).length = n := by
  induction n with
  | zero => simp [prefixCode]
  | succ k ih => simp [prefixCode, ih]

theorem prefixCode_bits (Z : Set ℕ) (n : ℕ) :
    ∀ x ∈ decodeSeq (prefixCode Z n), x ≤ 1 := by
  classical
  induction n with
  | zero => simp [prefixCode]
  | succ k ih =>
    intro x hx
    rw [prefixCode, decodeSeq_seqCode] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · rw [List.mem_singleton.mp hx]
      split_ifs <;> omega

/-- Prefix stability: earlier prefixes are literal truncations. -/
theorem prefixCode_take (Z : Set ℕ) {n m : ℕ} (hnm : n ≤ m) :
    (decodeSeq (prefixCode Z m)).take n = decodeSeq (prefixCode Z n) := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := by omega
    simp [prefixCode]
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · rw [prefixCode, decodeSeq_seqCode, List.take_append_of_le_length
        (by rw [prefixCode_length]; omega)]
      exact ih (by omega)
    · obtain rfl : n = k + 1 := by omega
      rw [List.take_of_length_le (by rw [prefixCode_length])]

/-- Bit stability: position `i` reads the same in every long-enough prefix. -/
theorem prefixCode_getD_stable (Z : Set ℕ) {i m : ℕ} (him : i < m) :
    (decodeSeq (prefixCode Z m)).getD i 0
      = (decodeSeq (prefixCode Z (i + 1))).getD i 0 := by
  rw [← prefixCode_take Z (show i + 1 ≤ m by omega), List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]

/-- **Layer 2**: the decoded path reduces to the separator — the recursion makes
one bounded query per step at the node-determined tag (audited property of the
implementation; the statement is ordinary Turing reducibility). -/
theorem pathSet_le_sep (Z : Set ℕ) : pathSet Z ≤ᵀ Z := by
  classical
  -- the prefix recursion, packed for `prec`
  have horacle : Nat.RecursiveIn {charFn Z} fun q =>
      charFn Z (3 * q.unpair.2.unpair.2) := by
    have hq : Nat.Partrec fun q => Part.some (3 * q.unpair.2.unpair.2) := by
      have : Primrec fun q : ℕ => 3 * q.unpair.2.unpair.2 :=
        Primrec.nat_mul.comp (.const 3)
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
    exact recursiveIn_comp_partrec
      (Nat.RecursiveIn.oracle (O := {charFn Z}) _ rfl) hq
  have hid : Nat.RecursiveIn {charFn Z} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair horacle
  have hpost : Nat.Partrec fun m => Part.some
      (seqCode (decodeSeq m.unpair.1.unpair.2.unpair.2 ++
        [if m.unpair.2 = 1 then 1 else 0])) := by
    have hih : Primrec fun m : ℕ => m.unpair.1.unpair.2.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
        (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    have hbit : Primrec fun m : ℕ => if m.unpair.2 = 1 then (1 : ℕ) else 0 :=
      Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 1))
        (.const 1) (.const 0)
    have hval : Primrec fun m : ℕ =>
        seqCode (decodeSeq m.unpair.1.unpair.2.unpair.2 ++
          [if m.unpair.2 = 1 then 1 else 0]) :=
      primrec_seqCode.comp
        (Primrec₂.comp (f := fun (l m : List ℕ) => l ++ m) Primrec.list_append
          (primrec_decodeSeq.comp hih)
          (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l)
            Primrec.list_cons hbit (.const [])))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  have hstep := hpost.recursiveIn.comp hpair
  have hprefix : Nat.RecursiveIn {charFn Z}
      (fun p => Part.some (prefixCode Z p.unpair.2)) := by
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
      simp [prefixCode]
    | succ y ih =>
      rw [← Nat.succ_eq_add_one]
      dsimp only
      rw [ih]
      simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind,
        Part.bind_some, Part.map_some, Nat.unpair_pair]
      by_cases hmem : 3 * prefixCode Z y ∈ Z
      · rw [if_pos hmem, if_pos rfl, prefixCode, if_pos hmem]
      · rw [if_neg hmem, if_neg (by omega), prefixCode, if_neg hmem]
  have hat : Nat.RecursiveIn {charFn Z}
      (fun i => Part.some (prefixCode Z (i + 1))) :=
    (recursiveIn_comp_primrec hprefix
      (Primrec₂.natPair.comp (.const 0) Primrec.succ)).of_eq fun i => by
      simp [Nat.unpair_pair]
  have hid' : Nat.RecursiveIn {charFn Z} fun i => Part.some i :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair' := hid'.pair hat
  have hpost' : Nat.Partrec fun z => Part.some
      (if (decodeSeq z.unpair.2).getD z.unpair.1 0 = 1 then 1 else 0) := by
    have hval : Primrec fun z : ℕ =>
        if (decodeSeq z.unpair.2).getD z.unpair.1 0 = 1 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec₂.comp (f := fun n i => (decodeSeq n).getD i 0) primrec_seqGet
          (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair))
        (.const 1)) (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost'.recursiveIn.comp hpair').of_eq fun i => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases h : (decodeSeq (prefixCode Z (i + 1))).getD i 0 = 1
  · rw [if_pos h, if_pos (show i ∈ pathSet Z from h)]
  · rw [if_neg h, if_neg (show i ∉ pathSet Z from h)]

/-! ### Correctness: the invariant and the child-selection argument -/

/-- The prefix is alive at every level at or above its own length. -/
def AliveForever (T : Set ℕ) (σ : ℕ) : Prop :=
  ∀ s, (decodeSeq σ).length ≤ s → hasExt T σ s

/-- An alive node at a stage past its length has an alive child there. -/
theorem alive_child_of_hasExt {T : Set ℕ} {σ s : ℕ}
    (hs : (decodeSeq σ).length + 1 ≤ s) (hσ : hasExt T σ s) :
    aliveAt T σ 0 s ∨ aliveAt T σ 1 s := by
  obtain ⟨i, hi, hmem, htake⟩ := hσ
  have hlen : (bitListOfIndex s i).length = s := bitListOfIndex_length s i
  set β := (bitListOfIndex s i).getD (decodeSeq σ).length 0 with hβdef
  have hβ : β ≤ 1 := by
    rw [hβdef, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact isBitSeqCode_seqCode_bitListOfIndex s i _
      (by rw [decodeSeq_seqCode]; exact List.getElem_mem _)
  have htakes : (bitListOfIndex s i).take ((decodeSeq σ).length + 1)
      = decodeSeq σ ++ [β] := by
    rw [List.take_add_one, htake, hβdef, List.getElem?_eq_getElem (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
    rfl
  have hchild : aliveAt T σ β s := by
    refine ⟨i, hi, hmem, ?_⟩
    rw [childCode, decodeSeq_seqCode, List.length_append, List.length_singleton]
    exact htakes
  rcases (by omega : β = 0 ∨ β = 1) with hb | hb
  · exact Or.inl (hb ▸ hchild)
  · exact Or.inr (hb ▸ hchild)

/-- **The child-selection lemma**: from an alive node whose child `b` eventually
dies, the first exactly-one event exists and its survivor is the other side. -/
theorem event_of_dying_child {T : Set ℕ}
    (hclosed : ∀ c ∈ T, ∀ k, seqCode ((decodeSeq c).take k) ∈ T)
    {σ : ℕ} (hσ : AliveForever T σ) {b : ℕ} (hb : b ≤ 1)
    (hdead : ¬AliveForever T (childCode σ b)) :
    ∃ s, evtFirst T σ s ∧ aliveAt T σ (1 - b) s := by
  classical
  rw [AliveForever] at hdead
  push Not at hdead
  obtain ⟨s₀, hs₀len, hs₀dead⟩ := hdead
  have hclen : (decodeSeq (childCode σ b)).length = (decodeSeq σ).length + 1 := by
    rw [childCode, decodeSeq_seqCode, List.length_append, List.length_singleton]
  rw [hclen] at hs₀len
  -- the dying child stays dead
  have hdead_ge : ∀ s, s₀ ≤ s → ¬aliveAt T σ b s := fun s hs halive =>
    hs₀dead (hasExt_mono hclosed (by rw [hclen]; omega) hs halive)
  -- exactly-one holds at `s₀`
  have hxone₀ : exactlyOne T σ s₀ := by
    have hσs₀ : hasExt T σ s₀ := hσ s₀ (by omega)
    rcases alive_child_of_hasExt (by omega) hσs₀ with h0 | h1
    · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · exact absurd h0 (hdead_ge s₀ le_rfl)
      · exact Or.inl ⟨h0, hdead_ge s₀ le_rfl⟩
    · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · exact Or.inr ⟨h1, hdead_ge s₀ le_rfl⟩
      · exact absurd h1 (hdead_ge s₀ le_rfl)
  -- the first exactly-one stage
  have hex : ∃ s, exactlyOne T σ s := ⟨s₀, hxone₀⟩
  set sStar := Nat.find hex with hsdef
  have hxone : exactlyOne T σ sStar := Nat.find_spec hex
  have hmin : ∀ s' < sStar, ¬exactlyOne T σ s' := fun s' hs' => Nat.find_min hex hs'
  refine ⟨sStar, ⟨hxone, hmin⟩, ?_⟩
  -- the survivor at `sStar` is the other side
  by_contra hother
  -- so the survivor at `sStar` is `b` itself — child `1 - b` is dead at `sStar`
  have hsb : aliveAt T σ b sStar ∧ ¬aliveAt T σ (1 - b) sStar := by
    rcases hxone with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · exact ⟨h0, by simpa using h1⟩
      · exact absurd h0 (by simpa using hother)
    · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · exact absurd h1 (by simpa using hother)
      · exact ⟨h1, by simpa using h0⟩
  -- child `1 - b` stays dead above `sStar`; child `b` stays dead above `s₀`
  have hslen : (decodeSeq σ).length + 1 ≤ sStar := by
    by_contra hlt
    exact not_hasExt_of_lt (by
      rw [childCode, decodeSeq_seqCode, List.length_append,
        List.length_singleton]
      omega) hsb.1
  have hother_ge : ∀ s, sStar ≤ s → ¬aliveAt T σ (1 - b) s := fun s hs halive =>
    hsb.2 (hasExt_mono hclosed (by
      rw [childCode, decodeSeq_seqCode, List.length_append, List.length_singleton]
      omega) hs halive)
  -- at a stage past both, some child is alive — contradiction
  set S := max s₀ sStar
  have hσS : hasExt T σ S := hσ S (le_trans (by omega) (le_max_left s₀ sStar))
  rcases alive_child_of_hasExt (le_trans (by omega) (le_max_right s₀ sStar)) hσS
    with h0 | h1
  · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · exact hdead_ge S (le_max_left _ _) h0
    · exact hother_ge S (le_max_right _ _) (by simpa using h0)
  · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · exact hother_ge S (le_max_right _ _) (by simpa using h1)
    · exact hdead_ge S (le_max_left _ _) h1

/-- The root is alive forever when the tree has a node at every level. -/
theorem aliveForever_root {T : Set ℕ} (htree : IsBinaryTreeCode T)
    (hlev : HasNodeAtEveryLevel T) : AliveForever T (seqCode []) := by
  intro s hs
  obtain ⟨c, hcT, hclen⟩ := hlev s
  obtain ⟨i, hi, hbl⟩ := exists_bitListOfIndex (decodeSeq c) (htree.1 c hcT)
  rw [hclen] at hi hbl
  refine ⟨i, hi, ?_, ?_⟩
  · rw [hbl, seqCode_decodeSeq]
    exact hcT
  · rw [decodeSeq_seqCode]
    simp

/-- An alive node is in the tree — canonical extension at its own length. -/
theorem mem_of_aliveForever {T : Set ℕ} {σ : ℕ} (hσ : AliveForever T σ) :
    σ ∈ T := by
  obtain ⟨i, hi, hmem, htake⟩ := hσ (decodeSeq σ).length le_rfl
  have hbl : bitListOfIndex (decodeSeq σ).length i = decodeSeq σ := by
    have htk : (bitListOfIndex (decodeSeq σ).length i).take
        (decodeSeq σ).length = bitListOfIndex (decodeSeq σ).length i :=
      List.take_of_length_le (by rw [bitListOfIndex_length])
    rw [← htk, htake]
  rw [hbl, seqCode_decodeSeq] at hmem
  exact hmem

section Direction

variable {Ω : OmegaPart} {h : IsTuringIdeal Ω} {T : Ω.InternalSet}
  {Z : Ω.InternalSet}

/-- The separator's bit answers transport to event facts through the compiled
injections. -/
private theorem sep_facts
    (hZ : SeparatesRanges (treeSepF h T) (treeSepG h T) Z) :
    (∀ σ s, leftDead T.1 σ s → 3 * σ ∈ Z.1) ∧
      ∀ σ s, rightDead T.1 σ s → 3 * σ ∉ Z.1 := by
  classical
  constructor
  · intro σ s hld
    have hmap : (treeSepF h T).MapsTo (Nat.pair σ s) (3 * σ) := by
      rw [treeSepF_mapsTo_iff, fval, Nat.unpair_pair]
      rw [if_pos hld]
    exact hZ.1 _ _ hmap
  · intro σ s hrd
    have hmap : (treeSepG h T).MapsTo (Nat.pair σ s) (3 * σ) := by
      rw [treeSepG_mapsTo_iff, gval, Nat.unpair_pair]
      rw [if_pos hrd]
    exact hZ.2 _ _ hmap

/-- **The invariant**: every decoded prefix is alive forever. -/
theorem prefixCode_aliveForever (htree : IsBinaryTreeCode T.1)
    (hlev : HasNodeAtEveryLevel T.1)
    (hZ : SeparatesRanges (treeSepF h T) (treeSepG h T) Z) :
    ∀ n, AliveForever T.1 (prefixCode Z.1 n) := by
  classical
  obtain ⟨hfZ, hgZ⟩ := sep_facts hZ
  intro n
  induction n with
  | zero => exact aliveForever_root htree hlev
  | succ k ih =>
    set σ := prefixCode Z.1 k with hσdef
    have hchild : prefixCode Z.1 (k + 1)
        = childCode σ (if 3 * σ ∈ Z.1 then 1 else 0) := rfl
    rw [hchild]
    by_contra hdead
    by_cases hmem : 3 * σ ∈ Z.1
    · rw [if_pos hmem] at hdead
      obtain ⟨s, hevt, hsurv⟩ :=
        event_of_dying_child htree.2 ih (by omega) hdead
      exact hgZ σ s ⟨hevt, by simpa using hsurv⟩ hmem
    · rw [if_neg hmem] at hdead
      obtain ⟨s, hevt, hsurv⟩ :=
        event_of_dying_child htree.2 ih (by omega) hdead
      exact hmem (hfZ σ s ⟨hevt, by simpa using hsurv⟩)

end Direction

end TreeSeparation

open TreeSeparation in
/-- **`separation → WKL`** over a Turing ideal: compile the tree to the two
internal injections, separate their ranges, and decode the separator to an
internal path. The path's internality uses only the separator's membership; the
tree and the injections enter only in correctness. -/
theorem weakKonigAt_of_disjointRangeSeparationAt {Ω : OmegaPart}
    (h : IsTuringIdeal Ω) (hsep : DisjointRangeSeparationAt Ω) :
    WeakKonigAt Ω := by
  classical
  intro T htree hlev
  obtain ⟨Z, hZ⟩ := hsep (treeSepF h T) (treeSepG h T)
    (treeSepF_isInjective h T) (treeSepG_isInjective h T)
    (treeSep_disjointRanges h T)
  have hinv := prefixCode_aliveForever htree hlev hZ
  refine ⟨⟨pathSet Z.1, h.mem_of_reducible Z.2 (pathSet_le_sep Z.1)⟩, fun n => ?_⟩
  refine ⟨prefixCode Z.1 n, mem_of_aliveForever (hinv n),
    prefixCode_length Z.1 n, fun i hi => ?_⟩
  rw [prefixCode_getD_stable Z.1 hi]
  constructor
  · intro h1
    exact h1
  · intro hmem
    exact hmem

end ReverseMathlib.Omega
