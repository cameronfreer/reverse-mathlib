/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.RecursiveIn
import Mathlib.Computability.PartrecCode

/-!
# Oracle codes: relativized coded computation (issue #49, feasibility slice)

Codes for oracle computations, mirroring `Nat.Partrec.Code` clause for clause with one
new base constructor `oracle` (query the oracle at the input), together with:

* `eval o c`: unbounded evaluation against a partial oracle `o : ℕ →. ℕ`;
* `evaln χ k c`: step-bounded evaluation against a total oracle `χ : ℕ → ℕ`, with the
  same input-guard discipline as mathlib's `evaln` (arguments bounded by the fuel), and
  `evaln_mono` / `evaln_sound` / `evaln_complete` relating it to `eval ↑χ`;
* `exists_code`: soundness and completeness against **singleton-oracle**
  `Nat.RecursiveIn` — `Nat.RecursiveIn {o} f ↔ ∃ c, eval o c = f`.

This is ambient classical mathematics about standard `ℕ`: nothing here is a
reverse-mathematics claim at any scope, and nothing registers in the catalog. It is the
first deliverable pair of the #49 feasibility gate (coded bounded oracle evaluation with
monotonicity; soundness/completeness against singleton-oracle `Nat.RecursiveIn`); the
jump set, the range-to-jump reduction, and the total injective jump enumeration build on
it in later slices, subject to that gate.

The proofs mirror `Mathlib/Computability/PartrecCode.lean` deliberately — same case
structure, same guard lemmas — so the relativization is auditable against its
unrelativized template.
-/

namespace ReverseMathlib.Omega

/-- Codes for oracle computations: `Nat.Partrec.Code` plus one base constructor
`oracle`, which queries the oracle at the input. -/
inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | oracle : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind' : OracleCode → OracleCode
  deriving DecidableEq, Inhabited

namespace OracleCode

/-- A code for the constant function, mirroring `Nat.Partrec.Code.const`. -/
protected def const : ℕ → OracleCode
  | 0 => zero
  | n + 1 => comp succ (OracleCode.const n)

/-- A code for the identity function. -/
protected def id : OracleCode :=
  pair left right

/-- Given a code `c` taking a pair as input, a code using `n` as the first argument to
`c`, mirroring `Nat.Partrec.Code.curry`. -/
def curry (c : OracleCode) (n : ℕ) : OracleCode :=
  comp c (pair (OracleCode.const n) OracleCode.id)

/-- An encoding of an `OracleCode` as a ℕ, mirroring `Nat.Partrec.Code.encodeCode`
with the five base constructors at `0`–`4` and the composite offset at `5`. -/
def encodeCode : OracleCode → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | oracle => 4
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 5
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 5
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 5

/-- The decoder, mirroring `Nat.Partrec.Code.ofNatCode`. -/
def ofNatCode : ℕ → OracleCode
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | 4 => oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => rfind' (ofNatCode m)

private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

instance instDenumerable : Denumerable OracleCode :=
  Denumerable.mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

theorem encodeCode_eq : Encodable.encode = encodeCode :=
  rfl

theorem ofNatCode_eq : Denumerable.ofNat OracleCode = ofNatCode :=
  rfl

/-- Unbounded evaluation of an oracle code against a partial oracle, mirroring
`Nat.Partrec.Code.eval`; the `oracle` clause is the oracle itself. -/
def eval (o : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | oracle => o
  | pair cf cg => fun n => Nat.pair <$> eval o cf n <*> eval o cg n
  | comp cf cg => fun n => eval o cg n >>= eval o cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval o cf a) fun y IH => do
        let i ← IH
        eval o cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval o cf (Nat.pair a (n + m))).map (· + m)

@[simp]
theorem eval_const (o : ℕ →. ℕ) : ∀ n m, eval o (OracleCode.const n) m = Part.some n
  | 0, _ => rfl
  | n + 1, m => by simp! [eval_const o n m]

@[simp]
theorem eval_id (o : ℕ →. ℕ) (n : ℕ) : eval o OracleCode.id n = Part.some n := by
  simp [OracleCode.id, eval, Seq.seq]

@[simp]
theorem eval_curry (o : ℕ →. ℕ) (c : OracleCode) (n x : ℕ) :
    eval o (curry c n) x = eval o c (Nat.pair n x) := by
  simp [curry, eval, Seq.seq]

/-- Step-bounded evaluation against a **total** oracle, mirroring
`Nat.Partrec.Code.evaln`: inputs are guarded by the fuel, and the `oracle` clause
returns the oracle's value at the (guarded) input. -/
def evaln (χ : ℕ → ℕ) : ℕ → OracleCode → ℕ → Option ℕ
  | 0, _ => fun _ => Option.none
  | k + 1, zero => fun n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ => fun n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left => fun n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right => fun n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, oracle => fun n => do
    guard (n ≤ k)
    return χ n
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evaln χ (k + 1) cf n <*> evaln χ (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let x ← evaln χ (k + 1) cg n
    evaln χ (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln χ (k + 1) cf a) fun y => do
        let i ← evaln χ k (prec cf cg) (Nat.pair a y)
        evaln χ (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln χ (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln χ k (rfind' cf) (Nat.pair a (m + 1))

theorem evaln_bound {χ : ℕ → ℕ} : ∀ {k c n x}, x ∈ evaln χ k c n → n < k
  | 0, c, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

set_option linter.flexible false in -- mirrors the template's exemption
theorem evaln_mono {χ : ℕ → ℕ} :
    ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln χ k₁ c n → x ∈ evaln χ k₂ c n
  | 0, k₂, c, n, x, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, n, x, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp only [Option.mem_def] at h ⊢
    induction c generalizing x n <;> rw [evaln] at h ⊢ <;> refine this hl' (fun h => ?_) h
    iterate 5 exact h
    case pair cf cg hf hg _ =>
      simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
        Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [Nat.unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp only [Nat.unpaired, bind, Nat.pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evaln_mono hl'

set_option linter.flexible false in -- mirrors the template's exemption
theorem evaln_sound {χ : ℕ → ℕ} : ∀ {k c n x}, x ∈ evaln χ k c n → x ∈ eval (↑χ) c n
  | 0, _, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    induction c generalizing x n <;>
        simp [eval, evaln, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 5 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evaln_mono k.le_succ h₁
          simp [evaln, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩,
            by simp [h₂]⟩
      · have := evaln_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

set_option linter.flexible false in -- mirrors the template's exemption
theorem evaln_complete {χ : ℕ → ℕ} {c n x} :
    x ∈ eval (↑χ) c n ↔ ∃ k, x ∈ evaln χ k c n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln χ (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      intro y hy hx
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evaln.eq_9, bind, Nat.unpaired, Nat.unpair_pair, Option.mem_def,
        Option.bind_eq_some_iff, Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ evaln χ (k + 1) (rfind' cf)
        (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evaln, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          (fun {i} hi => by
            simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
              hy₂ (Nat.succ_lt_succ hi)) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
      use a
      use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

/-! ### Soundness and completeness against singleton-oracle `Nat.RecursiveIn` -/

/-- Closure of singleton-oracle relativized computation under the `rfind'` shape,
mirroring `Nat.Partrec.rfind'`: derived from `rfind` plus computable input
rearrangement, remembering the offset through pairing. -/
theorem _root_.Nat.RecursiveIn.rfind'ClosureAux {o : ℕ →. ℕ} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {o} f) :
    Nat.RecursiveIn {o}
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) := by
  -- the searched function, with the (argument, offset) pair threaded through
  have hγ : Nat.RecursiveIn {o} (fun q : ℕ =>
      (Part.some (Nat.pair q.unpair.1.unpair.1 (q.unpair.2 + q.unpair.1.unpair.2)) :
        Part ℕ)) := by
    refine ((Nat.Partrec.of_primrec (Nat.Primrec.pair
        (Nat.Primrec.left.comp Nat.Primrec.left)
        (Nat.Primrec.add.comp (Nat.Primrec.pair Nat.Primrec.right
          (Nat.Primrec.right.comp Nat.Primrec.left))))).recursiveIn).of_eq fun q => by
      simp [Nat.unpaired]
  have hrearr : Nat.RecursiveIn {o} (fun q : ℕ =>
      f (Nat.pair q.unpair.1.unpair.1 (q.unpair.2 + q.unpair.1.unpair.2))) :=
    (Nat.RecursiveIn.comp hf hγ).of_eq fun q => by simp
  -- the raw search: F (pair a m) = rfind fun n => (· = 0) <$> f (pair a (n + m))
  have hF : Nat.RecursiveIn {o} (fun p : ℕ =>
      Nat.rfind fun n => (fun m => m = 0) <$>
        f (Nat.pair p.unpair.1 (n + p.unpair.2))) :=
    (Nat.RecursiveIn.rfind hrearr).of_eq fun p => by simp
  -- remember the input alongside the search result
  have hid : Nat.RecursiveIn {o} (fun p : ℕ => (Part.some p : Part ℕ)) :=
    Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec Nat.Primrec.id)
  have hpair : Nat.RecursiveIn {o} (fun p : ℕ =>
      Nat.pair <$> (Part.some p : Part ℕ) <*>
        Nat.rfind fun n => (fun m => m = 0) <$>
          f (Nat.pair p.unpair.1 (n + p.unpair.2))) :=
    Nat.RecursiveIn.pair hid hF
  -- project out result + offset
  have hδ : Nat.RecursiveIn {o} (fun z : ℕ =>
      (Part.some (z.unpair.2 + z.unpair.1.unpair.2) : Part ℕ)) := by
    refine ((Nat.Partrec.of_primrec (Nat.Primrec.add.comp
        (Nat.Primrec.pair Nat.Primrec.right
          (Nat.Primrec.right.comp Nat.Primrec.left)))).recursiveIn).of_eq fun z => by
      simp [Nat.unpaired]
  have := Nat.RecursiveIn.comp hδ hpair
  refine this.of_eq fun p => ?_
  simp only [Nat.unpaired, Part.bind_eq_bind, Part.map_eq_map, Seq.seq]
  ext x
  simp [Part.mem_map_iff, Part.mem_bind_iff, Nat.unpair_pair, eq_comm]

/-- **Soundness**: every oracle-code evaluation is recursive in its (singleton)
oracle. -/
theorem eval_recursiveIn (o : ℕ →. ℕ) : ∀ c : OracleCode, Nat.RecursiveIn {o} (eval o c)
  | zero => (Nat.RecursiveIn.zero).of_eq fun n => by simp [eval, pure, PFun.pure]; rfl
  | succ => Nat.RecursiveIn.succ
  | left => Nat.RecursiveIn.left
  | right => Nat.RecursiveIn.right
  | oracle => Nat.RecursiveIn.oracle o rfl
  | pair cf cg => Nat.RecursiveIn.pair (eval_recursiveIn o cf) (eval_recursiveIn o cg)
  | comp cf cg => Nat.RecursiveIn.comp (eval_recursiveIn o cf) (eval_recursiveIn o cg)
  | prec cf cg =>
    (Nat.RecursiveIn.prec (eval_recursiveIn o cf) (eval_recursiveIn o cg)).of_eq
      fun n => by simp [eval, Nat.unpaired]
  | rfind' cf => (eval_recursiveIn o cf).rfind'ClosureAux

/-- **Soundness and completeness against singleton-oracle `Nat.RecursiveIn`**: the
functions recursive in `{o}` are exactly the oracle-code evaluations against `o`. -/
theorem exists_code {f : ℕ →. ℕ} {o : ℕ →. ℕ} :
    Nat.RecursiveIn {o} f ↔ ∃ c : OracleCode, eval o c = f := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc ▸ eval_recursiveIn o c⟩
  induction h with
  | zero => exact ⟨zero, funext fun n => by simp [eval, pure, PFun.pure]; rfl⟩
  | succ => exact ⟨succ, rfl⟩
  | left => exact ⟨left, rfl⟩
  | right => exact ⟨right, rfl⟩
  | oracle g hg => exact ⟨oracle, by simpa [eval] using (Set.mem_singleton_iff.mp hg).symm⟩
  | pair hf hh ihf ihh =>
    rcases ihf with ⟨cf, rfl⟩; rcases ihh with ⟨ch, rfl⟩
    exact ⟨pair cf ch, rfl⟩
  | comp hf hh ihf ihh =>
    rcases ihf with ⟨cf, rfl⟩; rcases ihh with ⟨ch, rfl⟩
    exact ⟨comp cf ch, rfl⟩
  | prec hf hh ihf ihh =>
    rcases ihf with ⟨cf, rfl⟩; rcases ihh with ⟨ch, rfl⟩
    exact ⟨prec cf ch, funext fun n => by simp [eval, Nat.unpaired]⟩
  | rfind hf ihf =>
    rcases ihf with ⟨cf, rfl⟩
    refine ⟨comp (rfind' cf) (pair (pair left right) zero), ?_⟩
    funext n
    simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']

end OracleCode

end ReverseMathlib.Omega
