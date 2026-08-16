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
it in `ReverseMathlib.Omega.Jump`, each independently route-gated in
`scripts/MetaSmoke.lean`.

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

theorem encode_lt_pair (cf cg : OracleCode) :
    Encodable.encode cf < Encodable.encode (pair cf cg) ∧
      Encodable.encode cg < Encodable.encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode)
    (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this,
    lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

theorem encode_lt_comp (cf cg : OracleCode) :
    Encodable.encode cf < Encodable.encode (comp cf cg) ∧
      Encodable.encode cg < Encodable.encode (comp cf cg) := by
  have : Encodable.encode (pair cf cg) < Encodable.encode (comp cf cg) := by
    simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_prec (cf cg : OracleCode) :
    Encodable.encode cf < Encodable.encode (prec cf cg) ∧
      Encodable.encode cg < Encodable.encode (prec cf cg) := by
  have : Encodable.encode (pair cf cg) < Encodable.encode (prec cf cg) := by
    simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_rfind' (cf : OracleCode) :
    Encodable.encode cf < Encodable.encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  lia

theorem const_inj : ∀ {n₁ n₂}, OracleCode.const n₁ = OracleCode.const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [OracleCode.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

section primrecConstructors

open Primrec

theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp
              (Primrec.encode_iff.2 <| (Primrec.ofNat OracleCode).comp Primrec.fst)
              (Primrec.encode_iff.2 <| (Primrec.ofNat OracleCode).comp Primrec.snd))
        (Primrec₂.const 5)

theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp
              (Primrec.encode_iff.2 <| (Primrec.ofNat OracleCode).comp Primrec.fst)
              (Primrec.encode_iff.2 <| (Primrec.ofNat OracleCode).comp Primrec.snd))
        (Primrec₂.const 5)

theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp
              (Primrec.encode_iff.2 <| (Primrec.ofNat OracleCode).comp Primrec.fst)
              (Primrec.encode_iff.2 <| (Primrec.ofNat OracleCode).comp Primrec.snd))
        (Primrec₂.const 5)

theorem primrec_rfind' : Primrec rfind' :=
  Primrec.ofNat_iff.2 <|
    Primrec.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          Primrec.encode_iff.2 <| Primrec.ofNat OracleCode)
        (Primrec.const 5)

theorem primrec_const : Primrec OracleCode.const :=
  (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, OracleCode.const, Function.iterate_succ', -Function.iterate_succ]

theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <| primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const OracleCode.id)

end primrecConstructors

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

/-- **Table/oracle agreement whenever the fuel bounds every possible query**: two
oracles agreeing below the fuel produce identical bounded evaluations — every oracle
query inside `evaln χ k` is guarded to an argument `< k`. -/
theorem evaln_congr : ∀ {k c n} {χ χ' : ℕ → ℕ},
    (∀ m, m < k → χ m = χ' m) → evaln χ k c n = evaln χ' k c n
  | 0, c, n, χ, χ', _ => by simp [evaln]
  | k + 1, c, n, χ, χ', hag => by
    induction c generalizing n with rw [evaln, evaln]
    | oracle =>
      by_cases hn : n ≤ k
      · simp [hn, hag n (Nat.lt_succ_of_le hn)]
      · simp [hn]
    | pair cf cg hf hg => simp only [hf, hg]
    | comp cf cg hf hg => simp only [hf, hg]
    | prec cf cg hf hg =>
      have hrec : ∀ n, evaln χ k (prec cf cg) n = evaln χ' k (prec cf cg) n := fun n =>
        evaln_congr fun m hm => hag m (Nat.lt_succ_of_lt hm)
      simp only [hf, hg, hrec]
    | rfind' cf hf =>
      have hrec : ∀ n, evaln χ k (rfind' cf) n = evaln χ' k (rfind' cf) n := fun n =>
        evaln_congr fun m hm => hag m (Nat.lt_succ_of_lt hm)
      simp only [hf, hrec]

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

/-! ### The bounded evaluator is primitive recursive (table form)

The strong recursion is over encoded fuel–code pairs, consulting only genuinely
earlier rows; the dispatch on the raw code encoding is deliberately **flat** (a list
lookup for the five base constructors, an offset subtraction for the composites), so
elaboration stays linear and no `recOn` classifier is needed. `evaln_table` closes
the table/oracle agreement through `evaln_congr`. -/

section evalnPrimrec

open Encodable Denumerable

private def lup (L : List (List (Option ℕ))) (p : ℕ × OracleCode) (n : ℕ) : Option ℕ := do
  let l ← L[Encodable.encode p]?
  let o ← l[n]?
  o

/-- The per-entry dispatch of the row builder, by pattern match on the **raw
encoding** of the code (five base branches at `0`-`4`, then the parity decomposition
of the composite offset `5`) — one-level arithmetic case analysis with proper
equation lemmas, no code recursion, so no `recOn` classifier is needed. The
composite self-references (`prec`/`rfind'` at smaller fuel) go through the decoded
code `ofNat OracleCode ec`. -/
private def GbranchComposite (_σt : List ℕ) (L : List (List (Option ℕ)))
    (k' n e : ℕ) : Option ℕ :=
  let m := e.div2.div2
  cond e.bodd
    (cond e.div2.bodd
      -- rfind'
      (do
        let x ← lup L (k' + 1, ofNat OracleCode m) (Nat.pair n.unpair.1 n.unpair.2)
        x.casesOn (some n.unpair.2) fun _ =>
          lup L (k', ofNat OracleCode (e + 5))
            (Nat.pair n.unpair.1 (n.unpair.2 + 1)))
      -- prec
      (n.unpair.2.casesOn
        (lup L (k' + 1, ofNat OracleCode m.unpair.1) n.unpair.1) fun y => do
        let i ← lup L (k', ofNat OracleCode (e + 5)) (Nat.pair n.unpair.1 y)
        lup L (k' + 1, ofNat OracleCode m.unpair.2)
          (Nat.pair n.unpair.1 (Nat.pair y i))))
    (cond e.div2.bodd
      -- comp
      (do
        let x ← lup L (k' + 1, ofNat OracleCode m.unpair.2) n
        lup L (k' + 1, ofNat OracleCode m.unpair.1) x)
      -- pair
      (do
        let x ← lup L (k' + 1, ofNat OracleCode m.unpair.1) n
        let y ← lup L (k' + 1, ofNat OracleCode m.unpair.2) n
        some (Nat.pair x y)))

/-- The per-entry dispatch of the row builder: a **flat** case analysis on the raw
encoding — the five base branches by list lookup, the composite branch by offset
subtraction — with proper equation behavior and no nested case analysis, so both the
equation proofs and the primitive-recursiveness proof stay linear. -/
private def Gbranch (σt : List ℕ) (L : List (List (Option ℕ))) (k' n : ℕ)
    (ec : ℕ) : Option ℕ :=
  if ec < 5 then
    [some 0, some n.succ, some n.unpair.1, some n.unpair.2,
      some (σt.getD n 0)].getD ec none
  else
    GbranchComposite σt L k' n (ec - 5)

/-- The row builder for the strong recursion: row `L.length` decodes to a fuel–code
pair `(k, c)`; each entry `n < k` is computed from earlier rows through `lup`. -/
private def G (σt : List ℕ) (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × OracleCode) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Gbranch σt L k' n (Encodable.encode c)

private theorem evaln_map (χ : ℕ → ℕ) (k c n) :
    ((List.range k)[n]?.bind fun a => evaln χ k c a) = evaln χ k c n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln χ k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn

private theorem Gbranch_zero (σt L k' n) :
    Gbranch σt L k' n (Encodable.encode zero) = some 0 := rfl

private theorem Gbranch_succ (σt L k' n) :
    Gbranch σt L k' n (Encodable.encode succ) = some n.succ := rfl

private theorem Gbranch_left (σt L k' n) :
    Gbranch σt L k' n (Encodable.encode left) = some n.unpair.1 := rfl

private theorem Gbranch_right (σt L k' n) :
    Gbranch σt L k' n (Encodable.encode right) = some n.unpair.2 := rfl

private theorem Gbranch_oracle (σt L k' n) :
    Gbranch σt L k' n (Encodable.encode oracle) = some (σt.getD n 0) := rfl

private theorem Gbranch_of_composite (σt L k' n) (e : ℕ) :
    Gbranch σt L k' n (e + 5) = GbranchComposite σt L k' n e := by
  simp [Gbranch]

private theorem Gbranch_pair (σt L k' n) (cf cg : OracleCode) :
    Gbranch σt L k' n (Encodable.encode (pair cf cg)) = (do
      let x ← lup L (k' + 1, cf) n
      let y ← lup L (k' + 1, cg) n
      some (Nat.pair x y)) := by
  have he : Encodable.encode (pair cf cg) =
      Nat.bit false (Nat.bit false (Nat.pair cf.encodeCode cg.encodeCode)) + 5 := by
    simp [encodeCode_eq, encodeCode, Nat.bit_val]
  rw [he, Gbranch_of_composite]
  simp [GbranchComposite, ← encodeCode_eq]

private theorem Gbranch_comp (σt L k' n) (cf cg : OracleCode) :
    Gbranch σt L k' n (Encodable.encode (comp cf cg)) = (do
      let x ← lup L (k' + 1, cg) n
      lup L (k' + 1, cf) x) := by
  have he : Encodable.encode (comp cf cg) =
      Nat.bit false (Nat.bit true (Nat.pair cf.encodeCode cg.encodeCode)) + 5 := by
    simp [encodeCode_eq, encodeCode, Nat.bit_val]
  rw [he, Gbranch_of_composite]
  simp [GbranchComposite, ← encodeCode_eq]

private theorem Gbranch_prec (σt L k' n) (cf cg : OracleCode) :
    Gbranch σt L k' n (Encodable.encode (prec cf cg)) =
      (n.unpair.2.casesOn (lup L (k' + 1, cf) n.unpair.1) fun y => do
        let i ← lup L (k', prec cf cg) (Nat.pair n.unpair.1 y)
        lup L (k' + 1, cg) (Nat.pair n.unpair.1 (Nat.pair y i))) := by
  have he : Encodable.encode (prec cf cg) =
      Nat.bit true (Nat.bit false (Nat.pair cf.encodeCode cg.encodeCode)) + 5 := by
    simp [encodeCode_eq, encodeCode, Nat.bit_val]
  rw [he, Gbranch_of_composite]
  simp only [GbranchComposite, Nat.bodd_bit, Nat.div2_bit, cond_true]
  have hb : Nat.bit true (Nat.bit false (Nat.pair cf.encodeCode cg.encodeCode)) + 5 =
      Encodable.encode (prec cf cg) := he.symm
  rw [hb]
  simp [← encodeCode_eq]

private theorem Gbranch_rfind' (σt L k' n) (cf : OracleCode) :
    Gbranch σt L k' n (Encodable.encode (rfind' cf)) = (do
      let x ← lup L (k' + 1, cf) (Nat.pair n.unpair.1 n.unpair.2)
      x.casesOn (some n.unpair.2) fun _ =>
        lup L (k', rfind' cf) (Nat.pair n.unpair.1 (n.unpair.2 + 1))) := by
  have he : Encodable.encode (rfind' cf) =
      Nat.bit true (Nat.bit true cf.encodeCode) + 5 := by
    simp [encodeCode_eq, encodeCode, Nat.bit_val]
  rw [he, Gbranch_of_composite]
  simp only [GbranchComposite, Nat.bodd_bit, Nat.div2_bit, cond_true]
  have hb : Nat.bit true (Nat.bit true cf.encodeCode) + 5 =
      Encodable.encode (rfind' cf) := he.symm
  rw [hb]
  simp [← encodeCode_eq]

set_option linter.flexible false in -- template-mirroring case scripts
/-- The strong-recursion equation: `G` computes the next evaluation row from the
earlier rows. The oracle function is abstract (tied to the table only through `hχ`),
so the proof scripts never depend on the syntactic form of the table lookup. -/
private theorem G_correct (σt : List ℕ) (χ : ℕ → ℕ) (hχ : ∀ n, σt.getD n 0 = χ n)
    (p : ℕ) :
    G σt ((List.range p).map fun q =>
      (List.range (ofNat (ℕ × OracleCode) q).1).map
        (evaln χ (ofNat (ℕ × OracleCode) q).1 (ofNat (ℕ × OracleCode) q).2)) =
    some ((List.range (ofNat (ℕ × OracleCode) p).1).map
      (evaln χ (ofNat (ℕ × OracleCode) p).1 (ofNat (ℕ × OracleCode) p).2)) := by
  simp only [G, List.length_map, List.length_range, Option.some_inj]
  refine List.map_congr_left fun n hn => ?_
  have hp : List.range p = List.range (Nat.pair (ofNat (ℕ × OracleCode) p).1
      (Encodable.encode (ofNat (ℕ × OracleCode) p).2)) := by
    simp
  rw [hp]
  generalize (ofNat (ℕ × OracleCode) p).1 = k at hn ⊢
  generalize (ofNat (ℕ × OracleCode) p).2 = c at *
  simp only [List.mem_range] at hn
  rcases k with - | k'
  · simp at hn
  have nk : n ≤ k' := Nat.lt_succ_iff.mp hn
  have hg : ∀ {k₁ : ℕ} {c₁ : OracleCode} {n₁ : ℕ},
      Nat.pair k₁ (Encodable.encode c₁) < Nat.pair (k' + 1) (Encodable.encode c) →
      lup ((List.range (Nat.pair (k' + 1) (Encodable.encode c))).map fun q =>
          (List.range (Nat.unpair q).1).map
            (evaln χ (Nat.unpair q).1 (ofNat OracleCode (Nat.unpair q).2)))
        (k₁, c₁) n₁ =
        evaln χ k₁ c₁ n₁ := by
    intro k₁ c₁ n₁ hl
    have he : Encodable.encode (k₁, c₁) = Nat.pair k₁ (Encodable.encode c₁) := rfl
    simp [lup, he, List.getElem?_range hl, evaln_map, Bind.bind, Option.bind_map]
  change Gbranch σt _ k' n (Encodable.encode c) = evaln χ (k' + 1) c n
  obtain - | - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c
  · rw [Gbranch_zero]; simp [evaln, nk]
  · rw [Gbranch_succ]; simp [evaln, nk]
  · rw [Gbranch_left]; simp [evaln, nk]
  · rw [Gbranch_right]; simp [evaln, nk]
  · rw [Gbranch_oracle, hχ]; simp [evaln, nk]
  · -- pair
    rw [Gbranch_pair]
    simp [evaln, nk, Bind.bind, Functor.map, Seq.seq, pure]
    obtain ⟨lf, lg⟩ := encode_lt_pair cf cg
    rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
    cases evaln χ (k' + 1) cf n
    · rfl
    cases evaln χ (k' + 1) cg n <;> rfl
  · -- comp
    rw [Gbranch_comp]
    simp [evaln, nk, Bind.bind, pure]
    obtain ⟨lf, lg⟩ := encode_lt_comp cf cg
    rw [hg (Nat.pair_lt_pair_right _ lg)]
    cases evaln χ (k' + 1) cg n
    · rfl
    simp [hg (Nat.pair_lt_pair_right _ lf)]
  · -- prec
    rw [Gbranch_prec]
    simp [evaln, nk, Bind.bind, pure]
    obtain ⟨lf, lg⟩ := encode_lt_prec cf cg
    rw [hg (Nat.pair_lt_pair_right _ lf)]
    cases n.unpair.2
    · rfl
    simp only []
    rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
    cases evaln χ k' (prec cf cg) _
    · rfl
    simp [hg (Nat.pair_lt_pair_right _ lg)]
  · -- rfind'
    rw [Gbranch_rfind']
    simp [evaln, nk, Bind.bind, pure]
    have lf := encode_lt_rfind' cf
    rw [hg (Nat.pair_lt_pair_right _ lf)]
    rcases evaln χ (k' + 1) cf n with - | x
    · rfl
    cases x <;> simp
    rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]

section hG

open Primrec

private theorem hlup : Primrec fun p : List (List (Option ℕ)) × (ℕ × OracleCode) × ℕ =>
    lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst
      (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

/-- Shared accessor bundle for the branch combinators: the argument tuple is
`((table, rows), fuel-predecessor, entry) × composite-tag`. -/
private abbrev BTup : Type := ((List ℕ × List (List (Option ℕ))) × ℕ × ℕ) × ℕ

section branchCombinators

open Primrec

private theorem hσt : Primrec fun p : BTup => p.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
private theorem hL : Primrec fun p : BTup => p.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
private theorem hk' : Primrec fun p : BTup => p.1.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
private theorem hn : Primrec fun p : BTup => p.1.2.2 :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
private theorem hec : Primrec fun p : BTup => p.2 := Primrec.snd
private theorem hm : Primrec fun p : BTup => p.2.div2.div2 :=
  (nat_div2.comp nat_div2).comp hec
private theorem hm₁ : Primrec fun p : BTup => p.2.div2.div2.unpair.1 :=
  Primrec.fst.comp (Primrec.unpair.comp hm)
private theorem hm₂ : Primrec fun p : BTup => p.2.div2.div2.unpair.2 :=
  Primrec.snd.comp (Primrec.unpair.comp hm)
private theorem hn₁ : Primrec fun p : BTup => p.1.2.2.unpair.1 :=
  Primrec.fst.comp (Primrec.unpair.comp hn)
private theorem hn₂ : Primrec fun p : BTup => p.1.2.2.unpair.2 :=
  Primrec.snd.comp (Primrec.unpair.comp hn)
private theorem hkfuel : Primrec fun p : BTup => p.1.2.1 + 1 :=
  _root_.Primrec.succ.comp hk'
private theorem hcself : Primrec fun p : BTup => ofNat OracleCode (p.2 + 5) :=
  (Primrec.ofNat OracleCode).comp (_root_.Primrec.succ.comp <|
    _root_.Primrec.succ.comp <| _root_.Primrec.succ.comp <|
    _root_.Primrec.succ.comp <| _root_.Primrec.succ.comp hec)

private theorem hrf : Primrec fun p : BTup =>
    (do
      let x ← lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2)
        (Nat.pair p.1.2.2.unpair.1 p.1.2.2.unpair.2)
      x.casesOn (some p.1.2.2.unpair.2) fun _ =>
        lup p.1.1.2 (p.1.2.1, ofNat OracleCode (p.2 + 5))
          (Nat.pair p.1.2.2.unpair.1 (p.1.2.2.unpair.2 + 1)) : Option ℕ) := by
  refine Primrec.option_bind
    (hlup.comp <| hL.pair <| (hkfuel.pair ((Primrec.ofNat OracleCode).comp hm)).pair
      (Primrec₂.natPair.comp hn₁ hn₂)) ?_
  refine Primrec.nat_casesOn Primrec.snd
    (Primrec.option_some.comp (hn₂.comp Primrec.fst)) ?_
  exact ((hlup.comp <| (hL.comp Primrec.fst).pair <|
    ((hk'.comp Primrec.fst).pair (hcself.comp Primrec.fst)).pair
      (Primrec₂.natPair.comp (hn₁.comp Primrec.fst)
        (_root_.Primrec.succ.comp (hn₂.comp Primrec.fst)))).comp Primrec.fst).to₂

private theorem hpr : Primrec fun p : BTup =>
    (p.1.2.2.unpair.2.casesOn
      (lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2.unpair.1)
        p.1.2.2.unpair.1) fun y => do
      let i ← lup p.1.1.2 (p.1.2.1, ofNat OracleCode (p.2 + 5))
        (Nat.pair p.1.2.2.unpair.1 y)
      lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2.unpair.2)
        (Nat.pair p.1.2.2.unpair.1 (Nat.pair y i)) : Option ℕ) := by
  exact Primrec.nat_casesOn hn₂
    (hlup.comp <| hL.pair <|
      (hkfuel.pair ((Primrec.ofNat OracleCode).comp hm₁)).pair hn₁)
    ((Primrec.option_bind
      (hlup.comp <| (hL.comp Primrec.fst).pair <|
        ((hk'.comp Primrec.fst).pair (hcself.comp Primrec.fst)).pair
          (Primrec₂.natPair.comp (hn₁.comp Primrec.fst) Primrec.snd))
      ((hlup.comp <| ((hL.comp Primrec.fst).comp Primrec.fst).pair <|
        (((hkfuel.comp Primrec.fst).comp Primrec.fst).pair
          ((Primrec.ofNat OracleCode).comp <|
            (hm₂.comp Primrec.fst).comp Primrec.fst)).pair <|
        Primrec₂.natPair.comp ((hn₁.comp Primrec.fst).comp Primrec.fst)
          (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
            Primrec.snd)).to₂)).to₂)

private theorem hco : Primrec fun p : BTup =>
    (do
      let x ← lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2.unpair.2)
        p.1.2.2
      lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2.unpair.1) x :
      Option ℕ) := by
  refine Primrec.option_bind
    (hlup.comp <| hL.pair <|
      (hkfuel.pair ((Primrec.ofNat OracleCode).comp hm₂)).pair hn) ?_
  exact (hlup.comp <| (hL.comp Primrec.fst).pair <|
    ((hkfuel.comp Primrec.fst).pair
      ((Primrec.ofNat OracleCode).comp (hm₁.comp Primrec.fst))).pair
    Primrec.snd).to₂

private theorem hpa : Primrec fun p : BTup =>
    (do
      let x ← lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2.unpair.1)
        p.1.2.2
      let y ← lup p.1.1.2 (p.1.2.1 + 1, ofNat OracleCode p.2.div2.div2.unpair.2)
        p.1.2.2
      some (Nat.pair x y) : Option ℕ) := by
  exact Primrec.option_bind
    (hlup.comp <| hL.pair <|
      (hkfuel.pair ((Primrec.ofNat OracleCode).comp hm₁)).pair hn)
    ((Primrec.option_bind
      ((hlup.comp <| hL.pair <|
        (hkfuel.pair ((Primrec.ofNat OracleCode).comp hm₂)).pair hn).comp
          Primrec.fst)
      ((Primrec.option_some.comp
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst)
          Primrec.snd)).to₂)).to₂)

private theorem hcomposite : Primrec fun p : BTup =>
    GbranchComposite p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2 := by
  have := Primrec.cond (nat_bodd.comp hec)
    (Primrec.cond (nat_bodd.comp (nat_div2.comp hec)) hrf hpr)
    (Primrec.cond (nat_bodd.comp (nat_div2.comp hec)) hco hpa)
  exact this.of_eq fun p => rfl

end branchCombinators

/-- `Gbranch` is primitive recursive in all five arguments — the flat dispatch keeps
this a single `ite` over a literal list lookup and the composite offset. -/
private theorem hGbranch :
    Primrec fun p : BTup => Gbranch p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2 := by
  have hbase : Primrec fun p : BTup =>
      ([some 0, some p.1.2.2.succ, some p.1.2.2.unpair.1, some p.1.2.2.unpair.2,
        some (p.1.1.1.getD p.1.2.2 0)] : List (Option ℕ)).getD p.2 none := by
    refine (Primrec.list_getD (none : Option ℕ)).comp ?_ hec
    refine Primrec.list_cons.comp (Primrec.option_some.comp (_root_.Primrec.const 0)) ?_
    refine Primrec.list_cons.comp
      (Primrec.option_some.comp (_root_.Primrec.succ.comp hn)) ?_
    refine Primrec.list_cons.comp
      (Primrec.option_some.comp (Primrec.fst.comp (Primrec.unpair.comp hn))) ?_
    refine Primrec.list_cons.comp
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.unpair.comp hn))) ?_
    refine Primrec.list_cons.comp
      (Primrec.option_some.comp
        ((Primrec.list_getD (0 : ℕ)).comp hσt hn)) ?_
    exact _root_.Primrec.const []
  have hsub : Primrec fun p : BTup => ((p.1, p.2 - 5) : BTup) :=
    Primrec.fst.pair (nat_sub.comp hec (_root_.Primrec.const 5))
  have := Primrec.ite (nat_lt.comp hec (_root_.Primrec.const 5))
    hbase (hcomposite.comp hsub)
  exact this.of_eq fun p => rfl

end hG

section assembly

open Primrec

/-- `G` is primitive recursive (uncurried), with the table as the first component. -/
private theorem hG :
    Primrec fun p : List ℕ × List (List (Option ℕ)) => G p.1 p.2 := by
  have a : Primrec fun p : List ℕ × List (List (Option ℕ)) =>
      ofNat (ℕ × OracleCode) p.2.length :=
    (Primrec.ofNat (ℕ × OracleCode)).comp (Primrec.list_length.comp Primrec.snd)
  have k := Primrec.fst.comp a
  refine (Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k)
    ?_)).of_eq fun p => rfl
  refine .mk (Primrec.nat_casesOn (k.comp Primrec.fst)
    (_root_.Primrec.const Option.none) (.mk ?_))
  exact hGbranch.comp <|
    ((((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).pair
    (Primrec.encode.comp <| Primrec.snd.comp <|
      a.comp <| Primrec.fst.comp Primrec.fst))

/-- **The bounded table-oracle evaluator is primitive recursive**, with the table as
an explicit parameter: the strong recursion is over the encoded fuel–code pair, using
only genuinely earlier rows through `lup`. -/
theorem primrec_evaln_getD :
    Primrec fun q : (List ℕ × ℕ × ℕ) × ℕ =>
      evaln (q.1.1.getD · 0) q.1.2.1 (ofNat OracleCode q.1.2.2) q.2 := by
  have hstrong :
      Primrec₂ fun (σt : List ℕ) (q : ℕ) =>
        (List.range (ofNat (ℕ × OracleCode) q).1).map
          (evaln (σt.getD · 0) (ofNat (ℕ × OracleCode) q).1
            (ofNat (ℕ × OracleCode) q).2) :=
    Primrec.nat_strong_rec _ hG.to₂ fun σt q => G_correct σt _ (fun _ => rfl) q
  have hrow : Primrec fun q : (List ℕ × ℕ × ℕ) × ℕ =>
      (List.range q.1.2.1).map
        (evaln (q.1.1.getD · 0) q.1.2.1 (ofNat OracleCode q.1.2.2)) := by
    refine (hstrong.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).of_eq fun q => ?_
    simp
  refine (Primrec.option_bind (Primrec.list_getElem?.comp hrow Primrec.snd)
    Primrec.snd.to₂).of_eq fun q => ?_
  simp [evaln_map, Option.bind_map]

/-- **Table/oracle agreement through `evaln_congr`**: evaluating against the
length-`k` table of `χ` is evaluating against `χ` itself — the fuel bounds every
possible query. -/
theorem evaln_table (χ : ℕ → ℕ) (k : ℕ) (c : OracleCode) (n : ℕ) :
    evaln (((List.range k).map χ).getD · 0) k c n = evaln χ k c n :=
  evaln_congr fun m hm => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]

end assembly

end evalnPrimrec

end OracleCode

end ReverseMathlib.Omega
