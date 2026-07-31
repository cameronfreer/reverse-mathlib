/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Primrec.List
import ReverseMathlib.Omega.InternalSet

/-!
# The canonical finite-sequence coding (issue #22, slice 2)

**One** coding for finite sequences of naturals, used by every internal presentation:
`seqCode`/`decodeSeq` wrap mathlib's `Primcodable`/`Encodable` list encoding under project
names, because its encode/decode laws and list operations already carry `Primrec` support.
`Encodable.encode` is deliberately not exposed through the API.

Coding choice, documented: this is mathlib's `Encodable (List ℕ)` encoding (iterated
`Nat.pair` through `Denumerable`), **not** an object-arithmetic coding such as a β-function.
The choice is a presentation: a later presentation certificate connects this
primitive-recursive coding to the object-theory coding when the syntax layer arrives —
switching codings now would trade away ready computability lemmas for surface resemblance to
arithmetic syntax.

The coding is a **bijection**: `List ℕ` is denumerable, so every natural number is the
canonical code of exactly one finite sequence (`decodeSeq_seqCode` and `seqCode_decodeSeq`;
`seqEquiv` packages the equivalence). There is consequently no code-validity predicate —
one would be identically true. `IsBitSeqCode`/`IsBoundedSeqCode` describe sequence
*contents*, not code validity.
-/

namespace ReverseMathlib.Omega

/-- The canonical code of a finite sequence. -/
def seqCode (l : List ℕ) : ℕ :=
  Encodable.encode l

/-- Decoding; a two-sided inverse of `seqCode` since `List ℕ` is denumerable. -/
def decodeSeq (n : ℕ) : List ℕ :=
  ((Encodable.decode n : Option (List ℕ))).getD []

@[simp]
theorem decodeSeq_seqCode (l : List ℕ) : decodeSeq (seqCode l) = l := by
  simp [decodeSeq, seqCode]

@[simp]
theorem seqCode_decodeSeq (n : ℕ) : seqCode (decodeSeq n) = n := by
  simp [seqCode, decodeSeq, Denumerable.decode_eq_ofNat]

/-- The coding is injective (indeed bijective — see `seqEquiv`). -/
theorem seqCode_injective : Function.Injective seqCode := fun _ _ h => by
  simpa using congrArg decodeSeq h

/-- The canonical coding as an equivalence: every natural is a sequence code. -/
def seqEquiv : List ℕ ≃ ℕ where
  toFun := seqCode
  invFun := decodeSeq
  left_inv := decodeSeq_seqCode
  right_inv := seqCode_decodeSeq

/-- Encoding is primitive recursive. -/
theorem primrec_seqCode : Primrec seqCode :=
  Primrec.encode

/-- Decoding is primitive recursive. -/
theorem primrec_decodeSeq : Primrec decodeSeq :=
  Primrec.option_getD.comp Primrec.decode (.const [])

/-- Sequence length is primitive recursive on codes. -/
theorem primrec_seqLength : Primrec fun n => (decodeSeq n).length :=
  Primrec.list_length.comp primrec_decodeSeq

/-- Entry lookup (default `0`) is primitive recursive on codes. -/
theorem primrec_seqGet : Primrec₂ fun n i => (decodeSeq n).getD i 0 :=
  Primrec₂.comp (f := fun (l : List ℕ) (i : ℕ) => l.getD i 0) (Primrec.list_getD 0)
    (primrec_decodeSeq.comp .fst) .snd

/-- Truncation re-encoded is primitive recursive on codes. -/
theorem primrec_seqTake : Primrec₂ fun n k => seqCode ((decodeSeq n).take k) :=
  primrec_seqCode.comp
    (Primrec₂.comp Primrec.list_take .snd (primrec_decodeSeq.comp .fst))

/-- Append re-encoded is primitive recursive on codes. -/
theorem primrec_seqAppend : Primrec₂ fun m n => seqCode (decodeSeq m ++ decodeSeq n) :=
  primrec_seqCode.comp
    (Primrec₂.comp Primrec.list_append (primrec_decodeSeq.comp .fst)
      (primrec_decodeSeq.comp .snd))

/-! ### Finite transcripts

A **value table** records the first `L` values of a total function as a single code. It is
the normal form for a finite oracle transcript: the oracle is consulted only while the table
is built, and everything downstream is a pure function of the table. -/

/-- The first `L` values of `f`, as one code. -/
def valueTable (f : ℕ → ℕ) (L : ℕ) : ℕ :=
  seqCode ((List.range L).map f)

@[simp]
theorem decodeSeq_valueTable (f : ℕ → ℕ) (L : ℕ) :
    decodeSeq (valueTable f L) = (List.range L).map f := by
  rw [valueTable, decodeSeq_seqCode]

theorem valueTable_zero (f : ℕ → ℕ) : valueTable f 0 = 0 := by
  rw [valueTable, List.range_zero, List.map_nil]
  rfl

theorem valueTable_succ (f : ℕ → ℕ) (L : ℕ) :
    valueTable f (L + 1) = seqCode (decodeSeq (valueTable f L) ++ [f L]) := by
  rw [decodeSeq_valueTable, valueTable, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

theorem valueTable_eq_nat_rec (f : ℕ → ℕ) (L : ℕ) :
    valueTable f L = Nat.rec (motive := fun _ => ℕ) 0
      (fun y ih => seqCode (decodeSeq ih ++ [f y])) L := by
  induction L with
  | zero => exact valueTable_zero f
  | succ L ih => rw [valueTable_succ, ih]

/-- **The transcript is a finite oracle computation**, with a parameter: reading off the
first `p.unpair.2` values of the `p.unpair.1`-th member of a relatively computable family is
itself relatively computable, by primitive recursion on the length. This is the only place
the oracle is consulted in a transcript-then-verify reduction. -/
theorem valueTable_recursiveIn_param {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ → ℕ}
    (hf : Nat.RecursiveIn O fun m => Part.some (f m.unpair.1 m.unpair.2)) :
    Nat.RecursiveIn O fun p => Part.some (valueTable (f p.unpair.1) p.unpair.2) := by
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hpost : Primrec fun z : ℕ =>
      seqCode (decodeSeq z.unpair.2.unpair.2.unpair.2 ++ [z.unpair.1]) :=
    primrec_seqCode.comp
      (Primrec₂.comp (f := fun (l : List ℕ) (a : ℕ) => l ++ [a])
        (g := fun z : ℕ => decodeSeq z.unpair.2.unpair.2.unpair.2)
        (h := fun z : ℕ => z.unpair.1)
        Primrec.list_concat
        (primrec_decodeSeq.comp (hsnd.comp (hsnd.comp hsnd)))
        (Primrec.fst.comp Primrec.unpair))
  have hstep : Nat.RecursiveIn O fun m =>
      Part.some (seqCode (decodeSeq m.unpair.2.unpair.2 ++
        [f m.unpair.1 m.unpair.2.unpair.1])) := by
    have hg : Primrec fun m : ℕ => Nat.pair m.unpair.1 m.unpair.2.unpair.1 :=
      Primrec₂.comp (f := Nat.pair) (g := fun m : ℕ => m.unpair.1)
        (h := fun m : ℕ => m.unpair.2.unpair.1) Primrec₂.natPair
        (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    have h1 : Nat.RecursiveIn O fun m => Part.some (f m.unpair.1 m.unpair.2.unpair.1) :=
      (recursiveIn_comp_primrec hf hg).of_eq fun m => by simp only [Nat.unpair_pair]
    have h2 := recursiveIn_pair_total h1 (recursiveIn_of_primrec Primrec.id)
    exact (recursiveIn_comp_total (recursiveIn_of_primrec hpost) h2).of_eq fun m => by
      simp only [Nat.unpair_pair, id_eq]
  exact (recursiveIn_nat_rec_param (base := fun _ => 0)
    (step := fun a y ih => seqCode (decodeSeq ih ++ [f a y]))
    (recursiveIn_of_primrec (Primrec.const 0)) hstep).of_eq fun p => by
      rw [valueTable_eq_nat_rec]

/-- **The transcript is a finite oracle computation**: reading off the first `L` values of a
relatively computable total function is itself relatively computable. -/
theorem valueTable_recursiveIn {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O fun n => Part.some (f n)) :
    Nat.RecursiveIn O fun L => Part.some (valueTable f L) := by
  have hparam := valueTable_recursiveIn_param (f := fun _ => f)
    (recursiveIn_comp_primrec hf (Primrec.snd.comp Primrec.unpair))
  exact (recursiveIn_comp_primrec hparam
    (Primrec₂.comp (f := Nat.pair) (g := fun _ : ℕ => 0) (h := fun L : ℕ => L)
      Primrec₂.natPair (Primrec.const 0) Primrec.id)).of_eq fun L => by
    simp only [Nat.unpair_pair]

/-- A bit-sequence code: every entry is `0` or `1`. -/
def IsBitSeqCode (n : ℕ) : Prop :=
  ∀ x ∈ decodeSeq n, x ≤ 1

/-- A bounded-sequence code: every entry is at most `b`. -/
def IsBoundedSeqCode (b n : ℕ) : Prop :=
  ∀ x ∈ decodeSeq n, x ≤ b

theorem IsBitSeqCode.isBoundedSeqCode {n : ℕ} (h : IsBitSeqCode n) : IsBoundedSeqCode 1 n :=
  h

end ReverseMathlib.Omega
