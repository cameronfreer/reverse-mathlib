/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.SeparationGadget
import ReverseMathlib.Omega.Coding

/-!
# The separation gadget's computability layer (issue #42, slice 4)

Layer 2 of the gadget: the classifier as one oracle computation, the pure rows
with the classifier value as data, their primitive recursiveness, and the three
reductions to the join — the edge set, the left enumerator graph, and the right
enumerator graph, each `≤ᵀ f.graph ⊕ g.graph`. Everything here is generic in
arbitrary `F, G` and reaches only `hitClass`, the executable rows, and
`gadgetEdges` — never the eighteen-family relation or the semantic
characterizations (fine-dependency gates in `scripts/MetaSmoke.lean`).
-/

namespace ReverseMathlib.Omega

namespace SeparationGadget

/-! ### Layer 2: relative computability

The computational theorems are generic in arbitrary `F, G` and reach only
`hitClass`, the executable rows, and `gadgetEdges` — never the eighteen-family
relation or the semantic characterizations (fine-dependency gate in
`scripts/MetaSmoke.lean`). A row evaluation makes finitely many bounded oracle
queries: two per `hitClass` evaluation (one negative query to each graph), at
the source-indexed query point. -/

/-- **The classifier is one oracle computation**, proved once and composed into
everything downstream: two queries against the join — the `F` bit at the even
code, the `G` bit at the odd code — then a pure conditional. -/
theorem hitClass_recursiveIn (F G : Set ℕ) :
    Nat.RecursiveIn {charFn (joinSet F G)}
      (fun q => Part.some (hitClass F G q.unpair.1 q.unpair.2)) := by
  classical
  have hqF : Nat.Partrec fun q => Part.some (2 * Nat.pair q.unpair.2 q.unpair.1) := by
    have : Primrec fun q : ℕ => 2 * Nat.pair q.unpair.2 q.unpair.1 :=
      Primrec.nat_mul.comp (.const 2) (Primrec₂.natPair.comp
        (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hqG : Nat.Partrec fun q =>
      Part.some (2 * Nat.pair q.unpair.2 q.unpair.1 + 1) := by
    have : Primrec fun q : ℕ => 2 * Nat.pair q.unpair.2 q.unpair.1 + 1 :=
      Primrec.succ.comp (Primrec.nat_mul.comp (.const 2) (Primrec₂.natPair.comp
        (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hF := recursiveIn_comp_partrec
    (Nat.RecursiveIn.oracle (O := {charFn (joinSet F G)}) _ rfl) hqF
  have hG := recursiveIn_comp_partrec
    (Nat.RecursiveIn.oracle (O := {charFn (joinSet F G)}) _ rfl) hqG
  have hpair := hF.pair hG
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1 = 1 then 0 else if m.unpair.2 = 1 then 1 else 2) := by
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1 = 1 then 0 else if m.unpair.2 = 1 then 1 else 2 :=
      Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (.const 1))
        (.const 0)
        (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 1))
          (.const 1) (.const 2))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun q => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  by_cases hF' : Nat.pair q.unpair.2 q.unpair.1 ∈ F <;>
    by_cases hG' : Nat.pair q.unpair.2 q.unpair.1 ∈ G <;>
    simp [hitClass, FHits, two_mul_mem_joinSet, two_mul_add_one_mem_joinSet,
      hF', hG']

/-! ### Pure row assemblers: the class as data -/

/-- The left row with the classifier value supplied as data — pure, no sets. -/
def leftRowPure (v c : ℕ) : List ℕ :=
  if v % 2 = 0 then
    [ySpec 0 (v / 2), ySpec 1 (v / 2)]
  else
    let j := (xDecode v).1
    let n := (xDecode v).2.1
    let i := (xDecode v).2.2
    if j = 0 then
      [yChain 0 n i, if c = 2 then yAt 0 n i else yChain 2 n i]
    else if j = 1 then
      [yChain 1 n i, if c = 2 then yAt 1 n i else yChain 3 n i]
    else if j = 2 then
      [if i = 0 then yPlain n else yChain 2 n (i - 1),
        if c = 2 then yChain 2 n i else if c = 0 then yAt 0 n i else yAt 1 n i]
    else
      [if i = 0 then yPlain n else yChain 3 n (i - 1),
        if c = 2 then yChain 3 n i else if c = 0 then yAt 1 n i else yAt 0 n i]

/-- The left row's query point: the decoded `(n, i)` (unused on even codes). -/
def leftQuery (v : ℕ) : ℕ := Nat.pair (xDecode v).2.1 (xDecode v).2.2

theorem leftRow_eq_pure (F G : Set ℕ) (v : ℕ) :
    leftRow F G v = leftRowPure v
      (hitClass F G (leftQuery v).unpair.1 (leftQuery v).unpair.2) := by
  classical
  rw [leftRow, leftRowPure, leftQuery, Nat.unpair_pair]

/-- The right row with the classifier value supplied as data — pure, no sets. -/
def rightRowPure (v c : ℕ) : List ℕ :=
  if v % 2 = 0 then
    [xChain 2 (v / 2) 0, xChain 3 (v / 2) 0]
  else if v % 4 = 1 then
    let b := (ySpecDecode v).1
    let n := (ySpecDecode v).2
    if b = 0 then
      [xPlain n, if c = 2 then xChain 0 n 0
        else if c = 0 then xChain 2 n 0 else xChain 3 n 0]
    else
      [xPlain n, if c = 2 then xChain 1 n 0
        else if c = 0 then xChain 3 n 0 else xChain 2 n 0]
  else
    let j := (yChainDecode v).1
    let n := (yChainDecode v).2.1
    let i0 := (yChainDecode v).2.2
    if j = 0 then
      [xChain 0 n i0, if c = 2 then xChain 0 n (i0 + 1)
        else if c = 0 then xChain 2 n (i0 + 1) else xChain 3 n (i0 + 1)]
    else if j = 1 then
      [xChain 1 n i0, if c = 2 then xChain 1 n (i0 + 1)
        else if c = 0 then xChain 3 n (i0 + 1) else xChain 2 n (i0 + 1)]
    else if j = 2 then
      [xChain 2 n (i0 + 1), if c = 2 then xChain 2 n i0 else xChain 0 n i0]
    else
      [xChain 3 n (i0 + 1), if c = 2 then xChain 3 n i0 else xChain 1 n i0]

/-- The right row's query point, per the source's condition-index asymmetry:
index `0` for the specials, `i0 + 1` for chain `j ∈ {0, 1}`, `i0` for chain
`j ∈ {2, 3}` (unused on even codes). -/
def rightQuery (v : ℕ) : ℕ :=
  if v % 2 = 0 then 0
  else if v % 4 = 1 then Nat.pair (ySpecDecode v).2 0
  else
    let j := (yChainDecode v).1
    let n := (yChainDecode v).2.1
    let i0 := (yChainDecode v).2.2
    if j = 0 then Nat.pair n (i0 + 1)
    else if j = 1 then Nat.pair n (i0 + 1)
    else if j = 2 then Nat.pair n i0
    else Nat.pair n i0

theorem rightRow_eq_pure (F G : Set ℕ) (v : ℕ) :
    rightRow F G v = rightRowPure v
      (hitClass F G (rightQuery v).unpair.1 (rightQuery v).unpair.2) := by
  classical
  rcases yCases v with ⟨n, rfl⟩ | ⟨b, n, hb, rfl⟩ | ⟨j, n, i0, hj, rfl⟩
  · have h2 : yPlain n % 2 = 0 := by
      simp only [yPlain]
      omega
    rw [rightRow, rightRowPure, if_pos h2, if_pos h2]
  · obtain ⟨hm2, hm4⟩ := ySpec_mod b n
    rw [rightRow, rightRowPure, rightQuery, if_neg hm2, if_neg hm2, if_neg hm2,
      if_pos hm4, if_pos hm4, if_pos hm4, Nat.unpair_pair]
  · obtain ⟨hm2, hm4⟩ := yChain_mod j n i0
    rw [rightRow, rightRowPure, rightQuery, if_neg hm2, if_neg hm2, if_neg hm2,
      if_neg hm4, if_neg hm4, if_neg hm4, yChainDecode_yChain hj]
    have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj4 with rfl | rfl | rfl | rfl <;> simp [Nat.unpair_pair]

/-! ### Primitive recursiveness of the pure rows -/

private theorem primrec_seqPair : Primrec₂ fun a b => seqCode [a, b] :=
  (primrec_seqCode.comp
    (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l) Primrec.list_cons
      Primrec.fst
      (Primrec₂.comp (f := fun (x : ℕ) (l : List ℕ) => x :: l) Primrec.list_cons
        Primrec.snd (.const [])))).to₂

theorem primrec_xPlain : Primrec xPlain :=
  (Primrec.nat_mul.comp (.const 2) Primrec.id).of_eq fun _ => rfl

theorem primrec_yPlain : Primrec yPlain :=
  (Primrec.nat_mul.comp (.const 2) Primrec.id).of_eq fun _ => rfl

theorem primrec_xChainT :
    Primrec fun t : ℕ × ℕ × ℕ => xChain t.1 t.2.1 t.2.2 :=
  (Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (.const 8)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (.const 2) Primrec.fst))
    (.const 1)).of_eq fun _ => rfl

theorem primrec_ySpecT : Primrec fun t : ℕ × ℕ => ySpec t.1 t.2 :=
  (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 8) Primrec.snd)
      (Primrec.nat_mul.comp (.const 4) Primrec.fst))
    (.const 1)).of_eq fun _ => rfl

private theorem primrec_yChainT :
    Primrec fun t : ℕ × ℕ × ℕ => yChain t.1 t.2.1 t.2.2 :=
  (Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (.const 16)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (.const 4) Primrec.fst))
    (.const 3)).of_eq fun _ => rfl

private theorem primrec_yAtT :
    Primrec fun t : ℕ × ℕ × ℕ => yAt t.1 t.2.1 t.2.2 := by
  have h : Primrec fun t : ℕ × ℕ × ℕ =>
      if t.2.2 = 0 then ySpec t.1 t.2.1
        else yChain t.1 t.2.1 (t.2.2 - 1) :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (.const 0))
      (primrec_ySpecT.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (primrec_yChainT.comp (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (.const 1)))))
  exact h.of_eq fun _ => rfl

private theorem primrec_leftRowPureCode :
    Primrec₂ fun v c => seqCode (leftRowPure v c) := by
  have hv : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hcl : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hj : Primrec fun p : ℕ × ℕ => (xDecode p.1).1 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hv (.const 2)) (.const 4)
  have hn : Primrec fun p : ℕ × ℕ => (xDecode p.1).2.1 :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.nat_div.comp (Primrec.nat_div.comp hv (.const 2)) (.const 4)))
  have hi : Primrec fun p : ℕ × ℕ => (xDecode p.1).2.2 :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.nat_div.comp (Primrec.nat_div.comp hv (.const 2)) (.const 4)))
  have hyChain : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      yChain j (xDecode p.1).2.1 (xDecode p.1).2.2 := fun j =>
    primrec_yChainT.comp (Primrec.pair (.const j) (Primrec.pair hn hi))
  have hyAt : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      yAt j (xDecode p.1).2.1 (xDecode p.1).2.2 := fun j =>
    primrec_yAtT.comp (Primrec.pair (.const j) (Primrec.pair hn hi))
  have hyChainPred : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      yChain j (xDecode p.1).2.1 ((xDecode p.1).2.2 - 1) := fun j =>
    primrec_yChainT.comp (Primrec.pair (.const j)
      (Primrec.pair hn (Primrec.nat_sub.comp hi (.const 1))))
  have hfirst23 : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      if (xDecode p.1).2.2 = 0 then yPlain (xDecode p.1).2.1
        else yChain j (xDecode p.1).2.1 ((xDecode p.1).2.2 - 1) := fun j =>
    Primrec.ite (Primrec.eq.comp hi (.const 0)) (primrec_yPlain.comp hn)
      (hyChainPred j)
  have hc2 : PrimrecPred fun p : ℕ × ℕ => p.2 = 2 :=
    Primrec.eq.comp hcl (.const 2)
  have hc0 : PrimrecPred fun p : ℕ × ℕ => p.2 = 0 :=
    Primrec.eq.comp hcl (.const 0)
  have hbody : Primrec fun p : ℕ × ℕ =>
      seqCode (leftRowPure p.1 p.2) := by
    refine (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp hv (.const 2)) (.const 0))
      (primrec_seqPair.comp
        (primrec_ySpecT.comp (Primrec.pair (.const 0)
          (Primrec.nat_div.comp hv (.const 2))))
        (primrec_ySpecT.comp (Primrec.pair (.const 1)
          (Primrec.nat_div.comp hv (.const 2)))))
      (Primrec.ite (Primrec.eq.comp hj (.const 0))
        (primrec_seqPair.comp (hyChain 0)
          (Primrec.ite hc2 (hyAt 0) (hyChain 2)))
        (Primrec.ite (Primrec.eq.comp hj (.const 1))
          (primrec_seqPair.comp (hyChain 1)
            (Primrec.ite hc2 (hyAt 1) (hyChain 3)))
          (Primrec.ite (Primrec.eq.comp hj (.const 2))
            (primrec_seqPair.comp (hfirst23 2)
              (Primrec.ite hc2 (hyChain 2)
                (Primrec.ite hc0 (hyAt 0) (hyAt 1))))
            (primrec_seqPair.comp (hfirst23 3)
              (Primrec.ite hc2 (hyChain 3)
                (Primrec.ite hc0 (hyAt 1) (hyAt 0)))))))).of_eq fun p => ?_
    dsimp only [leftRowPure]
    split_ifs <;> rfl
  exact hbody.to₂

private theorem primrec_rightRowPureCode :
    Primrec₂ fun v c => seqCode (rightRowPure v c) := by
  have hv : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hcl : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hb : Primrec fun p : ℕ × ℕ => (ySpecDecode p.1).1 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hv (.const 4)) (.const 2)
  have hbn : Primrec fun p : ℕ × ℕ => (ySpecDecode p.1).2 :=
    Primrec.nat_div.comp (Primrec.nat_div.comp hv (.const 4)) (.const 2)
  have hj : Primrec fun p : ℕ × ℕ => (yChainDecode p.1).1 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hv (.const 4)) (.const 4)
  have hn : Primrec fun p : ℕ × ℕ => (yChainDecode p.1).2.1 :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.nat_div.comp (Primrec.nat_div.comp hv (.const 4)) (.const 4)))
  have hi0 : Primrec fun p : ℕ × ℕ => (yChainDecode p.1).2.2 :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.nat_div.comp (Primrec.nat_div.comp hv (.const 4)) (.const 4)))
  have hxChainSpec : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      xChain j (ySpecDecode p.1).2 0 := fun j =>
    primrec_xChainT.comp (Primrec.pair (.const j) (Primrec.pair hbn (.const 0)))
  have hxChainAt : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      xChain j (yChainDecode p.1).2.1 (yChainDecode p.1).2.2 := fun j =>
    primrec_xChainT.comp (Primrec.pair (.const j) (Primrec.pair hn hi0))
  have hxChainSucc : ∀ j : ℕ, Primrec fun p : ℕ × ℕ =>
      xChain j (yChainDecode p.1).2.1 ((yChainDecode p.1).2.2 + 1) := fun j =>
    primrec_xChainT.comp (Primrec.pair (.const j)
      (Primrec.pair hn (Primrec.succ.comp hi0)))
  have hc2 : PrimrecPred fun p : ℕ × ℕ => p.2 = 2 :=
    Primrec.eq.comp hcl (.const 2)
  have hc0 : PrimrecPred fun p : ℕ × ℕ => p.2 = 0 :=
    Primrec.eq.comp hcl (.const 0)
  have hbody : Primrec fun p : ℕ × ℕ =>
      seqCode (rightRowPure p.1 p.2) := by
    refine (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp hv (.const 2)) (.const 0))
      (primrec_seqPair.comp
        (primrec_xChainT.comp (Primrec.pair (.const 2)
          (Primrec.pair (Primrec.nat_div.comp hv (.const 2)) (.const 0))))
        (primrec_xChainT.comp (Primrec.pair (.const 3)
          (Primrec.pair (Primrec.nat_div.comp hv (.const 2)) (.const 0)))))
      (Primrec.ite (Primrec.eq.comp
        (Primrec.nat_mod.comp hv (.const 4)) (.const 1))
        (Primrec.ite (Primrec.eq.comp hb (.const 0))
          (primrec_seqPair.comp (primrec_xPlain.comp hbn)
            (Primrec.ite hc2 (hxChainSpec 0)
              (Primrec.ite hc0 (hxChainSpec 2) (hxChainSpec 3))))
          (primrec_seqPair.comp (primrec_xPlain.comp hbn)
            (Primrec.ite hc2 (hxChainSpec 1)
              (Primrec.ite hc0 (hxChainSpec 3) (hxChainSpec 2)))))
        (Primrec.ite (Primrec.eq.comp hj (.const 0))
          (primrec_seqPair.comp (hxChainAt 0)
            (Primrec.ite hc2 (hxChainSucc 0)
              (Primrec.ite hc0 (hxChainSucc 2) (hxChainSucc 3))))
          (Primrec.ite (Primrec.eq.comp hj (.const 1))
            (primrec_seqPair.comp (hxChainAt 1)
              (Primrec.ite hc2 (hxChainSucc 1)
                (Primrec.ite hc0 (hxChainSucc 3) (hxChainSucc 2))))
            (Primrec.ite (Primrec.eq.comp hj (.const 2))
              (primrec_seqPair.comp (hxChainSucc 2)
                (Primrec.ite hc2 (hxChainAt 2) (hxChainAt 0)))
              (primrec_seqPair.comp (hxChainSucc 3)
                (Primrec.ite hc2 (hxChainAt 3)
                  (hxChainAt 1)))))))).of_eq fun p => ?_
    dsimp only [rightRowPure]
    split_ifs <;> rfl
  exact hbody.to₂

/-! ### The three reductions to the join -/

private theorem primrec_leftQuery : Primrec leftQuery := by
  have hdd : Primrec fun v : ℕ => v / 2 / 4 :=
    Primrec.nat_div.comp (Primrec.nat_div.comp Primrec.id (.const 2)) (.const 4)
  exact (Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.unpair.comp hdd))
    (Primrec.snd.comp (Primrec.unpair.comp hdd))).of_eq fun v => rfl

private theorem primrec_rightQuery : Primrec rightQuery := by
  have hbn : Primrec fun v : ℕ => (ySpecDecode v).2 :=
    Primrec.nat_div.comp (Primrec.nat_div.comp Primrec.id (.const 4)) (.const 2)
  have hj : Primrec fun v : ℕ => (yChainDecode v).1 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.id (.const 4)) (.const 4)
  have hdd : Primrec fun v : ℕ => v / 4 / 4 :=
    Primrec.nat_div.comp (Primrec.nat_div.comp Primrec.id (.const 4)) (.const 4)
  have hn : Primrec fun v : ℕ => (yChainDecode v).2.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hdd)
  have hi0 : Primrec fun v : ℕ => (yChainDecode v).2.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hdd)
  have h := Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (.const 2)) (.const 0))
    (.const 0)
    (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp Primrec.id (.const 4)) (.const 1))
      (Primrec₂.natPair.comp hbn (.const 0))
      (Primrec.ite (Primrec.eq.comp hj (.const 0))
        (Primrec₂.natPair.comp hn (Primrec.succ.comp hi0))
        (Primrec.ite (Primrec.eq.comp hj (.const 1))
          (Primrec₂.natPair.comp hn (Primrec.succ.comp hi0))
          (Primrec.ite (Primrec.eq.comp hj (.const 2))
            (Primrec₂.natPair.comp hn hi0)
            (Primrec₂.natPair.comp hn hi0)))))
  refine h.of_eq fun v => ?_
  by_cases h2 : v % 2 = 0
  · simp [rightQuery, h2]
  · by_cases h4 : v % 4 = 1
    · simp [rightQuery, h2, h4]
    · by_cases hj0 : (yChainDecode v).1 = 0
      · simp [rightQuery, h2, h4, hj0]
      · by_cases hj1 : (yChainDecode v).1 = 1
        · simp [rightQuery, h2, h4, hj1]
        · by_cases hj2 : (yChainDecode v).1 = 2
          · simp [rightQuery, h2, h4, hj2]
          · simp [rightQuery, h2, h4, hj2]

/-- Layer 1 (raw): the left enumerator's graph — `Nat.pair v c` for `c` the code
of left code `v`'s neighbor row. -/
def gadgetLeftGraph (F G : Set ℕ) : Set ℕ :=
  {p | p.unpair.2 = seqCode (leftRow F G p.unpair.1)}

/-- Layer 1 (raw): the right enumerator's graph. -/
def gadgetRightGraph (F G : Set ℕ) : Set ℕ :=
  {p | p.unpair.2 = seqCode (rightRow F G p.unpair.1)}

/-- **The left enumerator reduces to the join**: compute the source-indexed
query, invoke the classifier once, postcompose the pure row code. -/
theorem gadgetLeftGraph_le_join (F G : Set ℕ) :
    gadgetLeftGraph F G ≤ᵀ joinSet F G := by
  classical
  have hq : Nat.Partrec fun p => Part.some (leftQuery p.unpair.1) :=
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
      (primrec_leftQuery.comp (Primrec.fst.comp Primrec.unpair)))).of_eq
      fun _ => rfl
  have hclass := recursiveIn_comp_partrec (hitClass_recursiveIn F G) hq
  have hid : Nat.RecursiveIn {charFn (joinSet F G)} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair hclass
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1.unpair.2 =
          seqCode (leftRowPure m.unpair.1.unpair.1 m.unpair.2) then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1.unpair.2 =
          seqCode (leftRowPure m.unpair.1.unpair.1 m.unpair.2) then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec₂.comp (f := fun v c => seqCode (leftRowPure v c))
          primrec_leftRowPureCode
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair)))
        (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  have hbridge := leftRow_eq_pure F G p.unpair.1
  by_cases h : p ∈ gadgetLeftGraph F G
  · rw [if_pos (by rw [← hbridge]; exact h), if_pos h]
  · rw [if_neg (fun hc => h (show p ∈ gadgetLeftGraph F G from by
      rw [gadgetLeftGraph, Set.mem_setOf_eq, hbridge]; exact hc)), if_neg h]

/-- **The right enumerator reduces to the join** — the mirror composition. -/
theorem gadgetRightGraph_le_join (F G : Set ℕ) :
    gadgetRightGraph F G ≤ᵀ joinSet F G := by
  classical
  have hq : Nat.Partrec fun p => Part.some (rightQuery p.unpair.1) :=
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
      (primrec_rightQuery.comp (Primrec.fst.comp Primrec.unpair)))).of_eq
      fun _ => rfl
  have hclass := recursiveIn_comp_partrec (hitClass_recursiveIn F G) hq
  have hid : Nat.RecursiveIn {charFn (joinSet F G)} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair hclass
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1.unpair.2 =
          seqCode (rightRowPure m.unpair.1.unpair.1 m.unpair.2) then 1 else 0) := by
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1.unpair.2 =
          seqCode (rightRowPure m.unpair.1.unpair.1 m.unpair.2) then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec₂.comp (f := fun v c => seqCode (rightRowPure v c))
          primrec_rightRowPureCode
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair)))
        (.const 1) (.const 0)
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  have hbridge := rightRow_eq_pure F G p.unpair.1
  by_cases h : p ∈ gadgetRightGraph F G
  · rw [if_pos (by rw [← hbridge]; exact h), if_pos h]
  · rw [if_neg (fun hc => h (show p ∈ gadgetRightGraph F G from by
      rw [gadgetRightGraph, Set.mem_setOf_eq, hbridge]; exact hc)), if_neg h]

private theorem mem_of_length_two {l : List ℕ} {b : ℕ} (hl : l.length = 2) :
    b ∈ l ↔ b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hl
  simp [List.getD]

/-- **The edge set reduces to the join** — through the two-entry left row: one
classifier evaluation, then equality against the row's two entries. No
existential search and no semantic adjacency theorem enters. -/
theorem gadgetEdges_le_join (F G : Set ℕ) :
    gadgetEdges F G ≤ᵀ joinSet F G := by
  classical
  have hq : Nat.Partrec fun p => Part.some (leftQuery p.unpair.1) :=
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
      (primrec_leftQuery.comp (Primrec.fst.comp Primrec.unpair)))).of_eq
      fun _ => rfl
  have hclass := recursiveIn_comp_partrec (hitClass_recursiveIn F G) hq
  have hid : Nat.RecursiveIn {charFn (joinSet F G)} fun q => Part.some q :=
    ((Nat.Partrec.of_primrec Nat.Primrec.id).recursiveIn).of_eq fun _ => rfl
  have hpair := hid.pair hclass
  have hpost : Nat.Partrec fun m => Part.some
      (if m.unpair.1.unpair.2 =
          (leftRowPure m.unpair.1.unpair.1 m.unpair.2).getD 0 0 then 1
        else if m.unpair.1.unpair.2 =
          (leftRowPure m.unpair.1.unpair.1 m.unpair.2).getD 1 0 then 1
        else 0) := by
    have hrow : Primrec fun m : ℕ =>
        leftRowPure m.unpair.1.unpair.1 m.unpair.2 := by
      have h := Primrec₂.comp (f := fun v c => seqCode (leftRowPure v c))
        primrec_leftRowPureCode
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair)
      exact (primrec_decodeSeq.comp h).of_eq fun m => by rw [decodeSeq_seqCode]
    have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    have hval : Primrec fun m : ℕ =>
        if m.unpair.1.unpair.2 =
          (leftRowPure m.unpair.1.unpair.1 m.unpair.2).getD 0 0 then 1
        else if m.unpair.1.unpair.2 =
          (leftRowPure m.unpair.1.unpair.1 m.unpair.2).getD 1 0 then 1
        else 0 :=
      Primrec.ite (Primrec.eq.comp hb
        ((Primrec.list_getD 0).comp hrow (.const 0)))
        (.const 1)
        (Primrec.ite (Primrec.eq.comp hb
          ((Primrec.list_getD 0).comp hrow (.const 1)))
          (.const 1) (.const 0))
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hval)).of_eq fun _ => rfl
  refine (hpost.recursiveIn.comp hpair).of_eq fun p => ?_
  simp only [charFn, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair]
  have hbridge := leftRow_eq_pure F G p.unpair.1
  have hlen : (leftRowPure p.unpair.1
      (hitClass F G (leftQuery p.unpair.1).unpair.1
        (leftQuery p.unpair.1).unpair.2)).length = 2 := by
    rw [← hbridge]
    exact leftRow_length F G p.unpair.1
  have hmem : p ∈ gadgetEdges F G ↔
      p.unpair.2 = (leftRowPure p.unpair.1
          (hitClass F G (leftQuery p.unpair.1).unpair.1
            (leftQuery p.unpair.1).unpair.2)).getD 0 0 ∨
        p.unpair.2 = (leftRowPure p.unpair.1
          (hitClass F G (leftQuery p.unpair.1).unpair.1
            (leftQuery p.unpair.1).unpair.2)).getD 1 0 := by
    rw [gadgetEdges, Set.mem_setOf_eq, hbridge, mem_of_length_two hlen]
  by_cases h : p ∈ gadgetEdges F G
  · rcases hmem.mp h with h1 | h1
    · rw [if_pos h1, if_pos h]
    · by_cases h0 : p.unpair.2 = (leftRowPure p.unpair.1
          (hitClass F G (leftQuery p.unpair.1).unpair.1
            (leftQuery p.unpair.1).unpair.2)).getD 0 0
      · rw [if_pos h0, if_pos h]
      · rw [if_neg h0, if_pos h1, if_pos h]
  · rw [if_neg (fun h1 => h (hmem.mpr (Or.inl h1))),
      if_neg (fun h1 => h (hmem.mpr (Or.inr h1))), if_neg h]

/-! ### Layer 3: the internal bigraph instance -/

/-- Membership normal form for the left enumerator graph. -/
theorem mem_gadgetLeftGraph_iff {F G : Set ℕ} {v c : ℕ} :
    Nat.pair v c ∈ gadgetLeftGraph F G ↔ c = seqCode (leftRow F G v) := by
  rw [gadgetLeftGraph, Set.mem_setOf_eq, Nat.unpair_pair]

/-- Membership normal form for the right enumerator graph. -/
theorem mem_gadgetRightGraph_iff {F G : Set ℕ} {v c : ℕ} :
    Nat.pair v c ∈ gadgetRightGraph F G ↔ c = seqCode (rightRow F G v) := by
  rw [gadgetRightGraph, Set.mem_setOf_eq, Nat.unpair_pair]

/-- Row-membership normal form for the edge set. -/
theorem mem_gadgetEdges_row {F G : Set ℕ} {n y : ℕ} :
    Nat.pair n y ∈ gadgetEdges F G ↔ y ∈ leftRow F G n := by
  rw [gadgetEdges, Set.mem_setOf_eq, Nat.unpair_pair]

end SeparationGadget

open SeparationGadget in
/-- **Layer 3: the gadget as an internal 2-regular bigraph.** Everything is
internal by ideal closure under the join of the two injection graphs plus the
three layer-2 reductions; the checked fields come from the structural layer —
`left_mem_iff` is definitional against the row-based edge set, and
`right_mem_iff` is exactly the reserved semantic coherence
`mem_rightRow_iff_mem_gadgetEdges`. The injections' properties (injectivity,
disjoint ranges) are NOT consumed here: the graph is a bigraph for arbitrary
internal `f, g`. -/
def gadgetBigraph {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    (f g : InternalFunction Ω) : InternalTwoRegularBigraph Ω where
  edges := ⟨gadgetEdges f.graph.1 g.graph.1,
    h.mem_of_reducible (h.join f.graph.2 g.graph.2) (gadgetEdges_le_join _ _)⟩
  leftEnum :=
    { graph := ⟨gadgetLeftGraph f.graph.1 g.graph.1,
        h.mem_of_reducible (h.join f.graph.2 g.graph.2)
          (gadgetLeftGraph_le_join _ _)⟩
      total := fun v => ⟨seqCode (leftRow f.graph.1 g.graph.1 v),
        mem_gadgetLeftGraph_iff.mpr rfl⟩
      singleValued := fun v y y' hy hy' => by
        rw [mem_gadgetLeftGraph_iff.mp hy, mem_gadgetLeftGraph_iff.mp hy'] }
  rightEnum :=
    { graph := ⟨gadgetRightGraph f.graph.1 g.graph.1,
        h.mem_of_reducible (h.join f.graph.2 g.graph.2)
          (gadgetRightGraph_le_join _ _)⟩
      total := fun v => ⟨seqCode (rightRow f.graph.1 g.graph.1 v),
        mem_gadgetRightGraph_iff.mpr rfl⟩
      singleValued := fun v y y' hy hy' => by
        rw [mem_gadgetRightGraph_iff.mp hy, mem_gadgetRightGraph_iff.mp hy'] }
  leftEnum_nodup := fun v c hc => by
    rw [mem_gadgetLeftGraph_iff.mp hc, decodeSeq_seqCode]
    exact leftRow_nodup _ _ v
  rightEnum_nodup := fun v c hc => by
    rw [mem_gadgetRightGraph_iff.mp hc, decodeSeq_seqCode]
    exact rightRow_nodup _ _ v
  left_mem_iff := fun n c y hc => by
    rw [mem_gadgetLeftGraph_iff.mp hc, decodeSeq_seqCode]
    exact mem_gadgetEdges_row.symm
  right_mem_iff := fun y c n hc => by
    rw [mem_gadgetRightGraph_iff.mp hc, decodeSeq_seqCode]
    exact mem_rightRow_iff_mem_gadgetEdges
  left_two_regular := fun v c hc => by
    rw [mem_gadgetLeftGraph_iff.mp hc, decodeSeq_seqCode]
    exact leftRow_length _ _ v
  right_two_regular := fun v c hc => by
    rw [mem_gadgetRightGraph_iff.mp hc, decodeSeq_seqCode]
    exact rightRow_length _ _ v

end ReverseMathlib.Omega
