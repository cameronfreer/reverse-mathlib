/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture: layer-indexed interface schemas

A model-indexed layer accepts interfaces of its registered schema type (checked by
definitional equality) and rejects everything else; schema-less layers keep the ambient
Prop-only behavior exactly. -/

/-- A dummy second-order part: a stand-in for the future `OmegaPart` in model-indexed
interface fixtures. -/
structure DummyOmegaPart where
  /-- The stand-in second-order collection. -/
  sets : Nat → Prop

/-- The interface schema of the fixture model layer. -/
abbrev FixModelInterface := DummyOmegaPart → Prop

rm_semantic_layer fixmodellayer "fixture model-indexed layer"
  interfaceSchema := FixModelInterface

/-- A model-indexed fixture predicate: acceptable at `fixmodellayer` only. -/
def fixModelPred : DummyOmegaPart → Prop := fun _ => True

/-- A second model-indexed predicate, for the schema-less-layer rejection test. -/
def fixModelPred2 : DummyOmegaPart → Prop := fun _ => False

rm_concept fixModelConcept where
  statement := "fixture statement for fixModelConcept"
  description := "fixture parent concept for model-indexed interface tests"

-- Accept: the interface type is definitionally the layer's schema.
rm_statement_variant fixModelVar where
  concept := fixModelConcept
  layer := fixmodellayer
  interface := fixModelPred
  description := "fixture model-indexed variant"

-- Reject: wrong type for the layer — a Prop where the schema demands `DummyOmegaPart → Prop`.
/--
error: concept catalog: interface 'FixtureProp' must have type 'FixModelInterface' (the interface schema of layer 'fixmodellayer') up to definitional equality
-/
#guard_msgs in
rm_statement_variant fixModelWrongType where
  concept := fixModelConcept
  layer := fixmodellayer
  interface := FixtureProp
  description := "rejected"

-- Reject: a model predicate on a schema-less layer — the ambient default is preserved exactly.
/-- error: concept catalog: interface 'fixModelPred2' must be a Prop-valued declaration -/
#guard_msgs in
rm_statement_variant fixModelWrongLayer where
  concept := fixModelConcept
  layer := fixlayer
  interface := fixModelPred2
  description := "rejected"

-- Reject: unknown interface-schema declaration.
/-- error: Unknown constant `NoSuchSchemaDecl` -/
#guard_msgs in
rm_semantic_layer fixbadschemalayer "rejected" interfaceSchema := NoSuchSchemaDecl

-- Reject: a term-level predicate is not a type-valued definition.
/--
error: concept catalog: interface schema 'fixModelPred' must be a universe-monomorphic type-valued definition (a name whose type is a Sort)
-/
#guard_msgs in
rm_semantic_layer fixbadschemalayer2 "rejected" interfaceSchema := fixModelPred

-- Reject: duplicate ownership of a model-indexed interface.
/--
error: concept catalog: Lean interface 'fixModelPred' is already owned by statement variant 'fixModelVar'
-/
#guard_msgs in
rm_statement_variant fixModelVarDup where
  concept := fixModelConcept
  layer := fixmodellayer
  interface := fixModelPred
  description := "rejected"
