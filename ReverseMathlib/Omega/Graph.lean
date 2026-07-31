/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Coding

/-!
# Graph-coded internal functions (issue #22, slice 2)

An internal function is **data**: an internal graph set of `Nat.pair x y` codes, with
totality and single-valuedness as properties. The ambient evaluation `eval` is derived
noncomputably for proof convenience — deliberately not a structure field, so it can never
smuggle untracked data past the internal-set discipline. Natural-valued paths and sections
are graph-coded functions; binary paths remain internal sets of bit-`1` positions.
-/

namespace ReverseMathlib.Omega

/-- A graph-coded internal function of a second-order part. -/
structure InternalFunction (Ω : OmegaPart) where
  /-- The graph, as an internal set of `Nat.pair x y` codes — the only data. -/
  graph : Ω.InternalSet
  /-- Totality. -/
  total : ∀ x, ∃ y, Nat.pair x y ∈ graph.1
  /-- Single-valuedness. -/
  singleValued : ∀ x y y', Nat.pair x y ∈ graph.1 → Nat.pair x y' ∈ graph.1 → y = y'

/-- `G` is the graph of the ambient function `f`. -/
def IsGraphOf (G : Set ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ x y, Nat.pair x y ∈ G ↔ f x = y

/-- The **relational surface**: `F` maps `x` to `y`. RM-facing statement definitions
(`WeakKonigAt`, `EFILCAt`, sections, `CountableHallAt`) are formulated entirely with
`MapsTo`/graph membership — never with `eval`, whose derivation uses choice; otherwise the
exact variant's statement closure would acquire `InternalFunction.eval` and ultimately
classical choice. `eval` is for proofs and adapter lemmas only, and a statement-dependency
gate pins the discipline. -/
def InternalFunction.MapsTo {Ω : OmegaPart} (F : InternalFunction Ω) (x y : ℕ) : Prop :=
  Nat.pair x y ∈ F.graph.1

theorem InternalFunction.existsUnique_mapsTo {Ω : OmegaPart} (F : InternalFunction Ω)
    (x : ℕ) : ∃! y, F.MapsTo x y := by
  obtain ⟨y, hy⟩ := F.total x
  exact ⟨y, hy, fun y' hy' => F.singleValued x y' y hy' hy⟩

open Classical in
/-- Ambient evaluation, derived **noncomputably** for proof convenience only — the
**least** output the graph assigns, which is exactly the value the oracle search below
finds. -/
noncomputable def InternalFunction.eval {Ω : OmegaPart} (F : InternalFunction Ω)
    (x : ℕ) : ℕ :=
  Nat.find (F.total x)

theorem InternalFunction.pair_eval_mem {Ω : OmegaPart} (F : InternalFunction Ω) (x : ℕ) :
    Nat.pair x (F.eval x) ∈ F.graph.1 := by
  classical
  exact Nat.find_spec (F.total x)

/-- Minimality of the derived evaluation (single-valuedness makes it vacuous
mathematically, but the search proof needs it directly). -/
theorem InternalFunction.eval_le {Ω : OmegaPart} (F : InternalFunction Ω) {x y : ℕ}
    (hy : Nat.pair x y ∈ F.graph.1) : F.eval x ≤ y := by
  classical
  exact Nat.find_le hy

/-- The graph decides evaluation. -/
theorem InternalFunction.graph_mem_iff {Ω : OmegaPart} (F : InternalFunction Ω)
    {x y : ℕ} : Nat.pair x y ∈ F.graph.1 ↔ F.eval x = y :=
  ⟨fun h => F.singleValued x _ _ (F.pair_eval_mem x) h, fun h => h ▸ F.pair_eval_mem x⟩

/-- The adapter between the relational surface and the proof-layer evaluation. -/
theorem InternalFunction.mapsTo_iff_eval_eq {Ω : OmegaPart} (F : InternalFunction Ω)
    {x y : ℕ} : F.MapsTo x y ↔ F.eval x = y :=
  F.graph_mem_iff

/-- The derived evaluation is what the graph codes. -/
theorem InternalFunction.isGraphOf_eval {Ω : OmegaPart} (F : InternalFunction Ω) :
    IsGraphOf F.graph.1 F.eval :=
  fun _ _ => F.graph_mem_iff

/-- **Unique graph lookup**: the evaluation of a total, single-valued internal function is
computable from its graph alone — search for the unique output using only the graph oracle.
Totality guarantees termination; single-valuedness makes the found value canonical. This is
the shared computational core of every internal-function lookup. -/
theorem InternalFunction.eval_recursiveIn_graph {Ω : OmegaPart} (F : InternalFunction Ω) :
    Nat.RecursiveIn {charFn F.graph.1} (fun x => Part.some (F.eval x)) := by
  classical
  have hsub : Nat.Partrec fun m => Part.some (1 - m) := by
    have : Primrec fun m : ℕ => 1 - m := Primrec.nat_sub.comp (.const 1) .id
    exact (Nat.Partrec.of_primrec (Primrec.nat_iff.mp this)).of_eq fun _ => rfl
  have hf := hsub.recursiveIn.comp
    (Nat.RecursiveIn.oracle (O := {charFn F.graph.1}) _ rfl)
  refine (Nat.RecursiveIn.rfind hf).of_eq fun x => ?_
  simp only [charFn, Part.map_eq_map, Part.bind_eq_bind, Part.bind_some, Part.map_some]
  rw [Part.eq_some_iff, Nat.mem_rfind]
  constructor
  · simp [F.pair_eval_mem x]
  · intro m hm
    have hnm : Nat.pair x m ∉ F.graph.1 := fun hc => absurd (F.eval_le hc) (by omega)
    simp [hnm]

/-- Graph-coded functions with equal graphs evaluate equally. -/
theorem InternalFunction.eval_congr {Ω : OmegaPart} {F G : InternalFunction Ω}
    (h : F.graph.1 = G.graph.1) (x : ℕ) : F.eval x = G.eval x :=
  (G.graph_mem_iff.mp (h ▸ F.pair_eval_mem x)).symm

end ReverseMathlib.Omega
