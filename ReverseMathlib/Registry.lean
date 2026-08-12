/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.DepGraph
import ReverseMathlib.Meta.Report
import ReverseMathlib.Meta.Commands
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Meta.Concepts
import ReverseMathlib.Meta.Interchange
import ReverseMathlib.Meta.InterfaceEncoder
import ReverseMathlib.Meta.BackendEvidence
import ReverseMathlib.Meta.CatalogExport
import ReverseMathlib.Ports.Catalog
import ReverseMathlib.Ports.ComputableAnalysis
import ReverseMathlib.Ports.FoundationBridge
import ReverseMathlib.Ports.CorpusAudit
import ReverseMathlib.Ports.Omega.Catalog
import ReverseMathlib.Ports.Omega.HallEfilc
import ReverseMathlib.Ports.Omega.RecWkl
import ReverseMathlib.Ports.Omega.WklEfilc
import ReverseMathlib.Ports.Omega.BoundedKonig
import ReverseMathlib.Ports.Omega.TwoRegularMatching
import ReverseMathlib.Ports.Omega.RangeSeparationFact
import ReverseMathlib.Ports.Mathlib.Hall
import ReverseMathlib.Ports.Mathlib.Konig

/-!
# Tooling and registry aggregate root

The second build root of this repository, alongside `ReverseMathlib.lean`. It aggregates the
dependency-mining commands, the evidence registry, and the mathlib port records
(`ReverseMathlib.Meta.*`, `ReverseMathlib.Ports.*`).

The mathematical root `ReverseMathlib.lean` **never** imports this module — ordinary users of
the mathematical library should not load metaprogramming machinery, and the mathematical axiom
audit stays interpretable. `scripts/check_sorry_boundary.py` enforces the separation;
`scripts/MetaAxiomAudit.lean` audits this root's declarations with the same standard-axiom
policy.
-/
