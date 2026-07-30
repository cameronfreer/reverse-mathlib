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

/-- A bit-sequence code: every entry is `0` or `1`. -/
def IsBitSeqCode (n : ℕ) : Prop :=
  ∀ x ∈ decodeSeq n, x ≤ 1

/-- A bounded-sequence code: every entry is at most `b`. -/
def IsBoundedSeqCode (b n : ℕ) : Prop :=
  ∀ x ∈ decodeSeq n, x ≤ b

theorem IsBitSeqCode.isBoundedSeqCode {n : ℕ} (h : IsBitSeqCode n) : IsBoundedSeqCode 1 n :=
  h

end ReverseMathlib.Omega
