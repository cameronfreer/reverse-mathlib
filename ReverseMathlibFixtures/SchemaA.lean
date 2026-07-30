/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlibFixtures.Base

/-! # Fixture SchemaA: registers layer `fixdupschemalayer` **with** an interface schema. -/

/-- Schema A's expected interface type. -/
abbrev FixSchemaA := Nat → Prop

rm_semantic_layer fixdupschemalayer "fixture layer, schema A" interfaceSchema := FixSchemaA
