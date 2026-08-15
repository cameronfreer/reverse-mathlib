/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.OracleCode
import ReverseMathlib.Omega.Computability
import Mathlib.Data.Nat.Nth

/-!
# The Turing jump over oracle codes (issue #49, feasibility slice)

The jump set of `A` (codes self-halting relative to `A`), with the four feasibility
deliverables of issue #49, each independently route-gated in `scripts/MetaSmoke.lean`:

* `jumpAccept_recursiveIn` — bounded acceptance is recursive in `A` through the table
  evaluator and the `evaln_congr` agreement; **`jumpSet` is never consulted**;
* `range_le_jump` — for any graph set `G`, the range is Turing reducible to
  `jumpSet G` through a **primitive-recursive curry map** and **one** jump query;
  the jump-enumeration construction plays no role;
* `jumpEnum_recursiveIn` / `jumpEnumGraph_le` — the executable first-acceptance
  enumeration (iterated bounded search, recursive in `A` alone, with infinitude
  entering only through termination) equals the `Nat.nth` specification, and its
  graph is Turing reducible to `A`; the range-to-jump theorem plays no role;
* `jumpEnum_injective` / `range_jumpEnum` — total injective enumeration with range
  exactly `jumpSet A`, infinitude by the padding family.

Ambient classical mathematics about standard `ℕ`: no reverse-mathematics claim at any
scope, and nothing here registers in the catalog. The Turing-ideal packaging of these
facts (the `JumpClosedAt` closure property and the equivalence with injection-range
existence) is deliberately **not** in this slice.
-/

namespace ReverseMathlib.Omega

open OracleCode Encodable Denumerable

section jump

open Classical in
/-- The total characteristic function of a set — `charFn` without the `Part`
wrapper; the two agree as partial oracles (`charFn_eq_coe`). -/
noncomputable def charFnTot (A : Set ℕ) : ℕ → ℕ := fun n =>
  if n ∈ A then 1 else 0

theorem charFn_eq_coe (A : Set ℕ) : charFn A = ↑(charFnTot A) := by
  funext n
  simp [charFn, charFnTot, PFun.coe_val]

/-- Stage-bounded acceptance: code `e` halts on its own index within fuel `k`,
relative to `A`. -/
noncomputable def jumpAccept (A : Set ℕ) (k e : ℕ) : Bool :=
  (evaln (charFnTot A) k (ofNat OracleCode e) e).isSome

set_option linter.flexible false in
theorem jumpAccept_mono (A : Set ℕ) {k k' e : ℕ} (h : k ≤ k')
    (ha : jumpAccept A k e) : jumpAccept A k' e := by
  simp only [jumpAccept, Option.isSome_iff_exists] at ha ⊢
  obtain ⟨x, hx⟩ := ha
  exact ⟨x, evaln_mono h hx⟩

/-- **The jump set**: codes that halt on their own index relative to `A`. -/
def jumpSet (A : Set ℕ) : Set ℕ :=
  {e | ∃ k, jumpAccept A k e}

set_option linter.flexible false in
/-- Membership in the jump is unbounded self-halting. -/
theorem mem_jumpSet_iff {A : Set ℕ} {e : ℕ} :
    e ∈ jumpSet A ↔ (eval (↑(charFnTot A)) (ofNat OracleCode e) e).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    simp only [jumpAccept, Option.isSome_iff_exists] at hk
    obtain ⟨x, hx⟩ := hk
    exact Part.dom_iff_mem.mpr ⟨x, evaln_sound hx⟩
  · intro hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨k, hk⟩ := evaln_complete.mp hx
    exact ⟨k, by simp [jumpAccept, Option.isSome_iff_exists]; exact ⟨x, hk⟩⟩

/-- **The padding family**: for every `j`, the code `comp (const 0) (const j)` halts
on every input — in particular on itself — and distinct `j` give distinct codes, so
the jump set is infinite. -/
theorem jumpSet_infinite (A : Set ℕ) : (jumpSet A).Infinite := by
  have hmem : ∀ j : ℕ,
      Encodable.encode (OracleCode.comp (OracleCode.const 0) (OracleCode.const j)) ∈ jumpSet A := by
    intro j
    rw [mem_jumpSet_iff, Denumerable.ofNat_encode]
    have : eval (↑(charFnTot A))
        (OracleCode.comp (OracleCode.const 0) (OracleCode.const j))
        (Encodable.encode (OracleCode.comp (OracleCode.const 0) (OracleCode.const j))) =
        Part.some 0 := by
      simp [eval]
    rw [this]
    trivial
  have hinj : Function.Injective fun j : ℕ =>
      Encodable.encode (OracleCode.comp (OracleCode.const 0) (OracleCode.const j)) := by
    intro j₁ j₂ h
    have := Encodable.encode_injective h
    injection this with h₁ h₂
    exact const_inj h₂
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-- First-stage acceptance of the pair `⟨e, k⟩`: accepted at fuel `k + 1` and not
before — each jump member is newly accepted at exactly one stage. -/
noncomputable def newAccept (A : Set ℕ) (p : ℕ) : Prop :=
  jumpAccept A (p.unpair.2 + 1) p.unpair.1 ∧ ¬ jumpAccept A p.unpair.2 p.unpair.1

theorem newAccept_unique {A : Set ℕ} {p q : ℕ} (hp : newAccept A p)
    (hq : newAccept A q) (h : p.unpair.1 = q.unpair.1) : p = q := by
  obtain ⟨hp₁, hp₂⟩ := hp
  obtain ⟨hq₁, hq₂⟩ := hq
  rw [h] at hp₁ hp₂
  rcases lt_trichotomy p.unpair.2 q.unpair.2 with hlt | heq | hgt
  · exact absurd (jumpAccept_mono A hlt hp₁) hq₂
  · have := Nat.pair_unpair p
    have hqq := Nat.pair_unpair q
    rw [← this, ← hqq, h, heq]
  · exact absurd (jumpAccept_mono A hgt hq₁) hp₂

/-- Every jump member is newly accepted at exactly one pair. -/
theorem exists_newAccept {A : Set ℕ} {e : ℕ} (he : e ∈ jumpSet A) :
    ∃ k, newAccept A (Nat.pair e k) := by
  obtain ⟨k₀, hk₀⟩ := he
  have hex : ∃ k, jumpAccept A k e := ⟨k₀, hk₀⟩
  classical
  have hk₁ : jumpAccept A (Nat.find hex) e := Nat.find_spec hex
  rcases hfind : Nat.find hex with - | k
  · rw [hfind] at hk₁
    simp [jumpAccept, evaln] at hk₁
  · refine ⟨k, ?_, ?_⟩ <;> simp only [Nat.unpair_pair]
    · rw [hfind] at hk₁
      exact hk₁
    · intro hacc
      have := Nat.find_min hex (m := k) (by rw [hfind]; exact Nat.lt_succ_self k)
      exact this hacc

/-- The newly-accepted pairs are infinite (through the padding family). -/
theorem newAccept_infinite (A : Set ℕ) : {p | newAccept A p}.Infinite := by
  have hmem : ∀ e : jumpSet A,
      Nat.pair e.1 (Classical.choose (exists_newAccept e.2)) ∈ {p | newAccept A p} :=
    fun e => Classical.choose_spec (exists_newAccept e.2)
  have hinf : (jumpSet A).Infinite := jumpSet_infinite A
  have : Infinite (jumpSet A) := hinf.to_subtype
  exact Set.infinite_of_injective_forall_mem
    (f := fun e : jumpSet A =>
      Nat.pair e.1 (Classical.choose (exists_newAccept e.2)))
    (by
      intro e₁ e₂ h
      have h1 := congrArg (fun p => Nat.unpair p) h
      simp only [Nat.unpair_pair] at h1
      exact Subtype.ext (congrArg Prod.fst h1)) hmem

end jump

section jumpEnum

/-- **The jump enumeration**: the code component of the `n`-th newly-accepted pair.
Total by construction; injective because each jump member is newly accepted at
exactly one pair; range exactly the jump set, with infinitude supplied by the
padding family. -/
noncomputable def jumpEnum (A : Set ℕ) (n : ℕ) : ℕ :=
  (Nat.nth (newAccept A) n).unpair.1

theorem newAccept_nth_mem (A : Set ℕ) (n : ℕ) :
    newAccept A (Nat.nth (newAccept A) n) :=
  Nat.nth_mem_of_infinite (newAccept_infinite A) n

/-- **Gate 3a — injectivity**: distinct indices give distinct newly-accepted pairs,
whose code components differ by first-stage uniqueness. -/
theorem jumpEnum_injective (A : Set ℕ) : Function.Injective (jumpEnum A) := by
  intro n₁ n₂ h
  have hne := Nat.nth_injective (newAccept_infinite A)
  by_contra hn
  have hp : Nat.nth (newAccept A) n₁ ≠ Nat.nth (newAccept A) n₂ :=
    fun hc => hn (hne hc)
  exact hp (newAccept_unique (newAccept_nth_mem A n₁) (newAccept_nth_mem A n₂) h)

/-- **Gate 4 — range**: the enumeration hits exactly the jump set. -/
theorem range_jumpEnum (A : Set ℕ) :
    Set.range (jumpEnum A) = jumpSet A := by
  ext e
  constructor
  · rintro ⟨n, rfl⟩
    have hm := newAccept_nth_mem A n
    exact ⟨(Nat.nth (newAccept A) n).unpair.2 + 1, hm.1⟩
  · intro he
    obtain ⟨k, hk⟩ := exists_newAccept he
    have : Nat.pair e k ∈ Set.range (Nat.nth (newAccept A)) := by
      rw [Nat.range_nth_of_infinite (newAccept_infinite A)]
      exact hk
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by rw [jumpEnum, hn, Nat.unpair_pair]⟩

end jumpEnum

section tableBuilder

/-- Building the length-`k` table of a function is recursive in any oracle computing
it: primitive recursion appending one oracle value per stage. -/
theorem table_recursiveIn {o : ℕ →. ℕ} {g : ℕ → ℕ}
    (hg : Nat.RecursiveIn {o} fun n => Part.some (g n)) :
    Nat.RecursiveIn {o} fun k =>
      Part.some (Encodable.encode ((List.range k).map g)) := by
  -- one step: from (stage, previous-table-code) to the extended table code
  have happend : Nat.Partrec fun q : ℕ => Part.some (Encodable.encode
      (((Encodable.decode (α := List ℕ) q.unpair.2.unpair.2).getD []) ++
        [q.unpair.1])) := by
    apply Nat.Partrec.of_primrec
    have : Primrec fun q : ℕ => Encodable.encode
        (((Encodable.decode (α := List ℕ) q.unpair.2.unpair.2).getD []) ++
          [q.unpair.1]) := by
      refine Primrec.encode.comp ?_
      refine Primrec.list_append.comp ?_ ?_
      · exact Primrec.option_getD.comp
          (Primrec.decode.comp <| Primrec.snd.comp <| Primrec.unpair.comp <|
            Primrec.snd.comp Primrec.unpair)
          (_root_.Primrec.const [])
      · exact Primrec.list_cons.comp
          (Primrec.fst.comp Primrec.unpair) (_root_.Primrec.const [])
    exact Primrec.nat_iff.mp this
  -- oracle value at the stage component
  have hy : Nat.Partrec fun q : ℕ => Part.some q.unpair.2.unpair.1 := by
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.id)
  have hgy : Nat.RecursiveIn {o} fun q : ℕ =>
      Part.some (g q.unpair.2.unpair.1) := by
    refine (Nat.RecursiveIn.comp hg hy.recursiveIn).of_eq fun q => ?_
    simp
  -- previous-table code, repackaged for the append step
  have hprev : Nat.RecursiveIn {o} fun q : ℕ =>
      Part.some q.unpair.2.unpair.2 := by
    refine Nat.Partrec.recursiveIn ?_
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.id)
  -- the paired input (g y, (0, i)) for the append step
  have hpre : Nat.RecursiveIn {o} fun q : ℕ =>
      Part.some (Nat.pair (g q.unpair.2.unpair.1)
        (Nat.pair 0 q.unpair.2.unpair.2)) := by
    have hzi : Nat.RecursiveIn {o} fun q : ℕ =>
        Part.some (Nat.pair 0 q.unpair.2.unpair.2) := by
      refine Nat.Partrec.recursiveIn ?_
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.pair Nat.Primrec.zero
        (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.id))
    refine (Nat.RecursiveIn.pair hgy hzi).of_eq fun q => ?_
    simp [Seq.seq]
  -- the full step function of the primitive recursion
  have hstep : Nat.RecursiveIn {o} fun q : ℕ => Part.some (Encodable.encode
      (((Encodable.decode (α := List ℕ) q.unpair.2.unpair.2).getD []) ++
        [g q.unpair.2.unpair.1])) := by
    refine (Nat.RecursiveIn.comp (Nat.Partrec.recursiveIn happend) hpre).of_eq
      fun q => ?_
    simp
  -- base and assembly
  have hbase : Nat.RecursiveIn {o} fun _ : ℕ =>
      Part.some (Encodable.encode ([] : List ℕ)) := by
    refine Nat.Partrec.recursiveIn ?_
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.const _
  have hrec := Nat.RecursiveIn.prec hbase hstep
  have hin : Nat.Partrec fun k : ℕ => Part.some (Nat.pair 0 k) := by
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.pair Nat.Primrec.zero Nat.Primrec.id
  refine (Nat.RecursiveIn.comp hrec hin.recursiveIn).of_eq fun k => ?_
  simp only [Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show (k + 1 : ℕ).rec (motive := fun _ => Part ℕ)
        (Part.some (Encodable.encode ([] : List ℕ)))
        (fun y IH => IH.bind fun i => Part.some (Encodable.encode
          (((Encodable.decode (α := List ℕ) i).getD []) ++ [g y]))) =
        ((k : ℕ).rec (motive := fun _ => Part ℕ)
          (Part.some (Encodable.encode ([] : List ℕ)))
          (fun y IH => IH.bind fun i => Part.some (Encodable.encode
            (((Encodable.decode (α := List ℕ) i).getD []) ++ [g y])))).bind
          (fun i => Part.some (Encodable.encode
            (((Encodable.decode (α := List ℕ) i).getD []) ++ [g k]))) from rfl]
      rw [ih]
      simp [List.range_succ]

end tableBuilder

section acceptRecursive

/-- **Bounded acceptance is recursive in the oracle set alone** — the computation
builds the stage table from `charFn A` and runs the primitive-recursive bounded
evaluator; `jumpSet A` is never queried. -/
theorem jumpAccept_recursiveIn (A : Set ℕ) :
    Nat.RecursiveIn {charFn A} fun p : ℕ =>
      Part.some (cond (jumpAccept A p.unpair.1 p.unpair.2) 1 0) := by
  -- the oracle computes its own total characteristic function
  have hχ : Nat.RecursiveIn {charFn A} fun n => Part.some (charFnTot A n) := by
    refine (Nat.RecursiveIn.oracle (O := {charFn A}) (charFn A) rfl).of_eq fun n => ?_
    rw [charFn_eq_coe]
    rfl
  -- the stage table, from the table builder
  have htable := table_recursiveIn (o := charFn A) hχ
  -- table code for the fuel component, paired with the original input
  have hfst : Nat.Partrec fun p : ℕ => Part.some p.unpair.1 := by
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.left.comp Nat.Primrec.id
  have hpack : Nat.RecursiveIn {charFn A} fun p : ℕ =>
      Part.some (Nat.pair
        (Encodable.encode ((List.range p.unpair.1).map (charFnTot A))) p) := by
    have h1 : Nat.RecursiveIn {charFn A} fun p : ℕ =>
        Part.some (Encodable.encode
          ((List.range p.unpair.1).map (charFnTot A))) := by
      refine (Nat.RecursiveIn.comp htable hfst.recursiveIn).of_eq fun p => ?_
      simp
    have hid : Nat.RecursiveIn {charFn A} fun p : ℕ => Part.some p :=
      Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec Nat.Primrec.id)
    refine (Nat.RecursiveIn.pair h1 hid).of_eq fun p => ?_
    simp [Seq.seq]
  -- pure postprocessing: decode the table, run the bounded evaluator, project isSome
  have hP : Primrec fun m : ℕ =>
      cond (evaln ((((Encodable.decode (α := List ℕ) m.unpair.1).getD []).getD · 0))
        m.unpair.2.unpair.1 (ofNat OracleCode m.unpair.2.unpair.2)
        m.unpair.2.unpair.2).isSome 1 0 := by
    have hσ : Primrec fun m : ℕ =>
        ((Encodable.decode (α := List ℕ) m.unpair.1).getD []) :=
      Primrec.option_getD.comp
        (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
        (_root_.Primrec.const [])
    have hk : Primrec fun m : ℕ => m.unpair.2.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have he : Primrec fun m : ℕ => m.unpair.2.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have hq : Primrec fun m : ℕ =>
        ((((Encodable.decode (α := List ℕ) m.unpair.1).getD []),
          (m.unpair.2.unpair.1, m.unpair.2.unpair.2)),
          m.unpair.2.unpair.2) :=
      (hσ.pair (hk.pair he)).pair he
    have hev := primrec_evaln_getD.comp hq
    exact (Primrec.cond (Primrec.option_isSome.comp hev)
      (_root_.Primrec.const 1) (_root_.Primrec.const 0))
  have hPnat : Nat.Partrec fun m : ℕ => (Part.some
      (cond (evaln ((((Encodable.decode (α := List ℕ) m.unpair.1).getD []).getD · 0))
        m.unpair.2.unpair.1 (ofNat OracleCode m.unpair.2.unpair.2)
        m.unpair.2.unpair.2).isSome 1 0) : Part ℕ) := by
    apply Nat.Partrec.of_primrec
    exact Primrec.nat_iff.mp hP
  refine (Nat.RecursiveIn.comp (Nat.Partrec.recursiveIn hPnat) hpack).of_eq
    fun p => ?_
  simp only [Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair, Encodable.encodek,
    Option.getD_some]
  rw [evaln_table]
  rfl

end acceptRecursive

section rangeToJump

/-- The preimage search relative to a graph oracle: on the pair `⟨v, x⟩` (the second
component deliberately ignored), hunt for the least `m` with `⟨m, v⟩` in the graph. -/
private theorem search_recursiveIn (G : Set ℕ) :
    Nat.RecursiveIn {charFn G} fun a : ℕ =>
      Nat.rfind fun m => (fun z => z = 0) <$>
        (charFn G (Nat.pair m a.unpair.1)).bind fun w => Part.some (1 - w) := by
  have htest : Nat.RecursiveIn {charFn G} fun q : ℕ =>
      (charFn G (Nat.pair q.unpair.2 q.unpair.1.unpair.1)).bind fun w =>
        Part.some (1 - w) := by
    have hre : Nat.Partrec fun q : ℕ =>
        Part.some (Nat.pair q.unpair.2 q.unpair.1.unpair.1) := by
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.id)
        (Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.id))
    have hflip : Nat.RecursiveIn {charFn G} fun w : ℕ =>
        (Part.some (1 - w) : Part ℕ) :=
      (Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec
        (Nat.Primrec.sub.comp (Nat.Primrec.pair (Nat.Primrec.const 1)
          Nat.Primrec.id)))).of_eq fun w => by simp [Nat.unpaired]
    have h1 := Nat.RecursiveIn.comp
      (Nat.RecursiveIn.oracle (O := {charFn G}) (charFn G) rfl) hre.recursiveIn
    have h2 := Nat.RecursiveIn.comp hflip h1
    refine h2.of_eq fun q => ?_
    simp
  refine (Nat.RecursiveIn.rfind htest).of_eq fun a => ?_
  congr 1
  funext m
  simp

set_option linter.flexible false in
/-- **Gate 2 — the curry reduction**: a fixed search code, curried with the sought
value, self-halts exactly when the value is in the range. The code map is the
primitive-recursive `v ↦ encode (OracleCode.curry cS v)`; membership needs one jump query. -/
theorem range_le_jump (G : Set ℕ) :
    {v : ℕ | ∃ m, Nat.pair m v ∈ G} ≤ᵀ jumpSet G := by
  classical
  -- the fixed search code
  obtain ⟨cS, hcS⟩ := exists_code.mp (search_recursiveIn G)
  -- the reduction: one jump query through the primitive-recursive code map
  have key : ∀ v : ℕ, (v ∈ {v : ℕ | ∃ m, Nat.pair m v ∈ G} ↔
      Encodable.encode (OracleCode.curry cS v) ∈ jumpSet G) := by
    intro v
    rw [mem_jumpSet_iff, Denumerable.ofNat_encode, ← charFn_eq_coe, eval_curry, hcS]
    simp only [Nat.unpair_pair]
    have hval : ∀ m : ℕ, ((fun z => decide (z = 0)) <$>
        ((charFn G (Nat.pair m v)).bind fun w => Part.some (1 - w))) =
        Part.some (decide (Nat.pair m v ∈ G)) := by
      intro m
      by_cases hmem : Nat.pair m v ∈ G <;> simp [charFn, hmem]
    constructor
    · rintro ⟨m, hm⟩
      classical
      have hex : ∃ m, Nat.pair m v ∈ G := ⟨m, hm⟩
      refine Part.dom_iff_mem.mpr ⟨Nat.find hex, ?_⟩
      rw [Nat.mem_rfind]
      constructor
      · rw [hval]
        simpa using Nat.find_spec hex
      · intro k hk
        rw [hval]
        simpa using Nat.find_min hex hk
    · intro hd
      obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hd
      rw [Nat.mem_rfind] at hn
      have := hn.1
      rw [hval] at this
      simp at this
      exact ⟨n, this⟩
  -- the characteristic reduction: one jump query through the primitive-recursive
  -- code map, then nothing else
  have hmap : Nat.Partrec fun v : ℕ =>
      Part.some (Encodable.encode (OracleCode.curry cS v)) := by
    apply Nat.Partrec.of_primrec
    exact Primrec.nat_iff.mp (Primrec.encode.comp
      (primrec₂_curry.comp (_root_.Primrec.const cS) _root_.Primrec.id))
  have h1 := Nat.RecursiveIn.comp
    (Nat.RecursiveIn.oracle (O := {charFn (jumpSet G)}) (charFn (jumpSet G)) rfl)
    hmap.recursiveIn
  refine h1.of_eq fun v => ?_
  simp only [Part.bind_eq_bind, Part.bind_some]
  classical
  simp only [charFn]
  congr 1
  by_cases hv : v ∈ {v : ℕ | ∃ m, Nat.pair m v ∈ G}
  · simp [hv, (key v).mp hv]
  · have : Encodable.encode (OracleCode.curry cS v) ∉ jumpSet G := fun hc => hv ((key v).mpr hc)
    simp [hv, this]

end rangeToJump

section enumRecursive

/-- Boolean form of first-stage acceptance: two bounded-acceptance queries. -/
noncomputable def newAcceptBool (A : Set ℕ) (p : ℕ) : Bool :=
  jumpAccept A (p.unpair.2 + 1) p.unpair.1 && ! jumpAccept A p.unpair.2 p.unpair.1

theorem newAccept_iff_bool {A : Set ℕ} {p : ℕ} :
    newAccept A p ↔ newAcceptBool A p = true := by
  simp [newAccept, newAcceptBool]

/-- The rfind-facing test (`0` = newly accepted), recursive in `A` through the two
bounded-acceptance queries — `jumpSet` is never consulted. -/
private theorem testNew_recursiveIn (A : Set ℕ) :
    Nat.RecursiveIn {charFn A} fun p : ℕ =>
      Part.some (cond (newAcceptBool A p) 0 1) := by
  have hJA := jumpAccept_recursiveIn A
  have h1 : Nat.RecursiveIn {charFn A} fun p : ℕ =>
      Part.some (cond (jumpAccept A (p.unpair.2 + 1) p.unpair.1) 1 0) := by
    have hre : Nat.Partrec fun p : ℕ =>
        Part.some (Nat.pair (p.unpair.2 + 1) p.unpair.1) := by
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.pair
        (Nat.Primrec.succ.comp (Nat.Primrec.right.comp Nat.Primrec.id))
        (Nat.Primrec.left.comp Nat.Primrec.id)
    refine (Nat.RecursiveIn.comp hJA hre.recursiveIn).of_eq fun p => ?_
    simp
  have h2 : Nat.RecursiveIn {charFn A} fun p : ℕ =>
      Part.some (cond (jumpAccept A p.unpair.2 p.unpair.1) 1 0) := by
    have hre : Nat.Partrec fun p : ℕ =>
        Part.some (Nat.pair p.unpair.2 p.unpair.1) := by
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.id)
        (Nat.Primrec.left.comp Nat.Primrec.id)
    refine (Nat.RecursiveIn.comp hJA hre.recursiveIn).of_eq fun p => ?_
    simp
  have hcombine : Nat.Partrec fun w : ℕ =>
      Part.some (cond ((w.unpair.1 == 1) && (w.unpair.2 == 0)) 0 1) := by
    apply Nat.Partrec.of_primrec
    have : Primrec fun w : ℕ =>
        cond ((w.unpair.1 == 1) && (w.unpair.2 == 0)) 0 1 := by
      refine Primrec.cond
        (?_ : Primrec fun w : ℕ => (w.unpair.1 == 1) && (w.unpair.2 == 0))
        (_root_.Primrec.const 0) (_root_.Primrec.const 1)
      have hb : ∀ w : ℕ, ((w.unpair.1 == 1) && (w.unpair.2 == 0)) =
          cond (w.unpair.1 == 1) (w.unpair.2 == 0) false := by
        intro w
        cases w.unpair.1 == 1 <;> simp
      refine (Primrec.cond
        (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair)
          (_root_.Primrec.const 1))
        (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
          (_root_.Primrec.const 0))
        (_root_.Primrec.const false)).of_eq fun w => (hb w).symm
    exact Primrec.nat_iff.mp this
  refine (Nat.RecursiveIn.comp (Nat.Partrec.recursiveIn hcombine)
    (Nat.RecursiveIn.pair h1 h2)).of_eq fun p => ?_
  simp only [Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair, newAcceptBool]
  cases h1v : jumpAccept A (p.unpair.2 + 1) p.unpair.1 <;>
    cases h2v : jumpAccept A p.unpair.2 p.unpair.1 <;> rfl

private theorem testNew_zero_iff {A : Set ℕ} (v : ℕ) :
    cond (newAcceptBool A v) 0 1 = 0 ↔ newAccept A v := by
  rw [newAccept_iff_bool]
  cases newAcceptBool A v <;> simp

set_option linter.unusedSimpArgs false in -- the rec-unfold simp is load-bearing
-- (removing it breaks the ih rewrite) but is misdetected as unused
/-- **Gate 3b — executable enumeration with its specification**: iterated bounded
search over the acceptance test computes the `Nat.nth`-defined pair stream. Recursive
in `A` alone; the infinitude enters only through termination of each search. -/
theorem nthNewAccept_recursiveIn (A : Set ℕ) :
    Nat.RecursiveIn {charFn A} fun n : ℕ =>
      Part.some (Nat.nth (newAccept A) n) := by
  have hinf := newAccept_infinite A
  have hf : Nat.RecursiveIn {charFn A} fun q : ℕ =>
      Part.some (cond (newAcceptBool A q.unpair.2) 0 1) := by
    have hre : Nat.Partrec fun q : ℕ => Part.some q.unpair.2 := by
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.right.comp Nat.Primrec.id
    refine (Nat.RecursiveIn.comp (testNew_recursiveIn A) hre.recursiveIn).of_eq
      fun q => ?_
    simp
  have hFirst := Nat.RecursiveIn.rfind hf
  have hStep0 := hf.rfind'ClosureAux
  have hpackstep : Nat.Partrec fun q : ℕ =>
      Part.some (Nat.pair 0 (q.unpair.2.unpair.2 + 1)) := by
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.pair Nat.Primrec.zero
      (Nat.Primrec.succ.comp (Nat.Primrec.right.comp
        (Nat.Primrec.right.comp Nat.Primrec.id)))
  have hstepc := Nat.RecursiveIn.comp hStep0 hpackstep.recursiveIn
  have hrec := Nat.RecursiveIn.prec hFirst hstepc
  have hin : Nat.Partrec fun n : ℕ => Part.some (Nat.pair 0 n) := by
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.pair Nat.Primrec.zero Nat.Primrec.id
  have hmono : StrictMono (Nat.nth (newAccept A)) := Nat.nth_strictMono hinf
  have hlower : ∀ n, IsLeast
      {i | newAccept A i ∧ ∀ k < n, Nat.nth (newAccept A) k < i}
      (Nat.nth (newAccept A) n) := fun n => Nat.isLeast_nth_of_infinite hinf n
  refine (Nat.RecursiveIn.comp hrec hin.recursiveIn).of_eq fun n => ?_
  simp only [Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  induction n with
  | zero =>
      simp only [Nat.rec_zero]
      refine Part.eq_some_iff.mpr ?_
      refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
      · simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff]
        have := Nat.nth_mem_of_infinite hinf 0
        rw [← testNew_zero_iff (A := A)] at this
        simp [this]
      · intro m hm
        simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff]
        have hnm : ¬ newAccept A m := fun hp =>
          absurd ((hlower 0).2 ⟨hp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩)
            (Nat.not_le.mpr hm)
        rw [← testNew_zero_iff (A := A)] at hnm
        simpa using hnm
  | succ k ih =>
      simp only [Nat.rec_add_one]
      rw [ih]
      simp only [Part.bind_some, Nat.unpaired]
      refine Part.eq_some_iff.mpr ?_
      refine (Part.mem_map_iff _).mpr ?_
      have hgt : Nat.nth (newAccept A) k + 1 ≤ Nat.nth (newAccept A) (k + 1) :=
        hmono (Nat.lt_succ_self k)
      refine ⟨Nat.nth (newAccept A) (k + 1) - (Nat.nth (newAccept A) k + 1),
        Nat.mem_rfind.mpr ⟨?_, ?_⟩, ?_⟩
      · simp only [Nat.unpair_pair, Part.map_eq_map, Part.map_some,
          Part.mem_some_iff]
        rw [Nat.sub_add_cancel hgt]
        have := Nat.nth_mem_of_infinite hinf (k + 1)
        rw [← testNew_zero_iff (A := A)] at this
        simp [this]
      · intro d' hd'
        simp only [Nat.unpair_pair, Part.map_eq_map, Part.map_some,
          Part.mem_some_iff]
        have hnm : ¬ newAccept A (d' + (Nat.nth (newAccept A) k + 1)) := by
          intro hp
          have hmem : d' + (Nat.nth (newAccept A) k + 1) ∈
              {i | newAccept A i ∧ ∀ j < k + 1, Nat.nth (newAccept A) j < i} := by
            refine ⟨hp, fun j hj => ?_⟩
            have : Nat.nth (newAccept A) j ≤ Nat.nth (newAccept A) k :=
              hmono.monotone (Nat.lt_succ_iff.mp hj)
            omega
          have := (hlower (k + 1)).2 hmem
          omega
        rw [← testNew_zero_iff (A := A)] at hnm
        simpa using hnm
      · simp only [Nat.unpair_pair]
        rw [Nat.sub_add_cancel hgt]

/-- **Gate 3 — the enumeration is computable in `A`**, hence so is its graph. -/
theorem jumpEnum_recursiveIn (A : Set ℕ) :
    Nat.RecursiveIn {charFn A} fun n : ℕ => Part.some (jumpEnum A n) := by
  have hfst : Nat.Partrec fun q : ℕ => Part.some q.unpair.1 := by
    apply Nat.Partrec.of_primrec
    exact Nat.Primrec.left.comp Nat.Primrec.id
  refine (Nat.RecursiveIn.comp hfst.recursiveIn
    (nthNewAccept_recursiveIn A)).of_eq fun n => ?_
  simp [jumpEnum]

/-- **Gate 3 — the graph reduction**: the graph of the jump enumeration is Turing
reducible to `A`. -/
theorem jumpEnumGraph_le (A : Set ℕ) :
    {q : ℕ | jumpEnum A q.unpair.1 = q.unpair.2} ≤ᵀ A := by
  classical
  have hEnum := jumpEnum_recursiveIn A
  have h1 : Nat.RecursiveIn {charFn A} fun q : ℕ =>
      Part.some (jumpEnum A q.unpair.1) := by
    have hfst : Nat.Partrec fun q : ℕ => Part.some q.unpair.1 := by
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.left.comp Nat.Primrec.id
    refine (Nat.RecursiveIn.comp hEnum hfst.recursiveIn).of_eq fun q => ?_
    simp
  have hid : Nat.RecursiveIn {charFn A} fun q : ℕ => Part.some q :=
    Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec Nat.Primrec.id)
  have heq : Nat.Partrec fun w : ℕ =>
      Part.some (cond (w.unpair.1 == w.unpair.2.unpair.2) 1 0) := by
    apply Nat.Partrec.of_primrec
    have : Primrec fun w : ℕ => cond (w.unpair.1 == w.unpair.2.unpair.2) 1 0 :=
      Primrec.cond (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.snd.comp Primrec.unpair))))
        (_root_.Primrec.const 1) (_root_.Primrec.const 0)
    exact Primrec.nat_iff.mp this
  refine (Nat.RecursiveIn.comp (Nat.Partrec.recursiveIn heq)
    (Nat.RecursiveIn.pair h1 hid)).of_eq fun q => ?_
  simp only [Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Nat.unpair_pair, charFn]
  by_cases hq : jumpEnum A q.unpair.1 = q.unpair.2
  · simp [hq]
  · have : (jumpEnum A q.unpair.1 == q.unpair.2) = false := by
      simpa using hq
    simp [hq, this]

end enumRecursive


end ReverseMathlib.Omega
