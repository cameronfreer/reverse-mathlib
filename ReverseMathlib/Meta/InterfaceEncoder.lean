/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean

/-!
# The `lean-interface-expr/1` canonical interface encoding (importer side)

The importer-side implementation of the backend-evidence fingerprint encoding
(bridge contract: reverse-mathlib-foundation `docs/evidence-schema.md`): canonical
structural payloads for declarations, the recursive semantic-interface closure, and
exact manifest comparison. This is a deliberate second implementation of the same
specification — the production evidence artifact is the main cross-implementation
conformance fixture, and `scripts/MetaSmoke.lean` pins exact encoded-string vectors
against conceptual drift shared by both sides.

Encoding rules: `Expr` constructors encoded directly (no pretty-printing); `mdata`
stripped; binder names ignored, binder info kept; universe parameters normalized by
position; explicit name/literal escaping; free variables and metavariables are hard
errors. Payloads: type always; bodies of definitions **and opaque definitions** (an
owned opaque can carry semantic meaning); constructor types for inductives;
theorem **statements only** — proof bodies never enter. Constructors are attributed to
their inductive; a recursor enqueues **every** inductive of its (possibly mutual)
group.
-/

open Lean

namespace ReverseMathlib.Meta.InterfaceExpr

def escapeStr (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c = '\\' then "\\\\" else if c = '"' then "\\\"" else c.toString)) ""

def encodeName : Name → String
  | .anonymous => "_"
  | .str p s => encodeName p ++ ".\"" ++ escapeStr s ++ "\""
  | .num p n => encodeName p ++ ".#" ++ toString n

def levelParamIdx (ps : List Name) (n : Name) : Except String Nat :=
  match ps.idxOf? n with
  | some i => .ok i
  | none => .error s!"unbound universe parameter {n}"

partial def encodeLevel (ps : List Name) : Level → Except String String
  | .zero => .ok "0"
  | .succ l => do return s!"(s {← encodeLevel ps l})"
  | .max a b => do return s!"(max {← encodeLevel ps a} {← encodeLevel ps b})"
  | .imax a b => do return s!"(imax {← encodeLevel ps a} {← encodeLevel ps b})"
  | .param n => do return s!"(u {← levelParamIdx ps n})"
  | .mvar _ => .error "level metavariable"

def biTag : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "si"
  | .instImplicit => "ii"

partial def encodeExpr (ps : List Name) : Expr → Except String String
  | .bvar i => .ok s!"(b {i})"
  | .fvar _ => .error "free variable in closed declaration"
  | .mvar _ => .error "metavariable in closed declaration"
  | .sort u => do return s!"(S {← encodeLevel ps u})"
  | .const n ls => do
      let ls' ← ls.mapM (encodeLevel ps)
      return s!"(c {encodeName n}{String.join (ls'.map (" " ++ ·))})"
  | .app f a => do return s!"(a {← encodeExpr ps f} {← encodeExpr ps a})"
  | .lam _ t b bi => do
      return s!"(l {biTag bi} {← encodeExpr ps t} {← encodeExpr ps b})"
  | .forallE _ t b bi => do
      return s!"(P {biTag bi} {← encodeExpr ps t} {← encodeExpr ps b})"
  | .letE _ t v b _ => do
      return s!"(L {← encodeExpr ps t} {← encodeExpr ps v} {← encodeExpr ps b})"
  | .lit (.natVal n) => .ok s!"(n {n})"
  | .lit (.strVal s) => .ok s!"(str \"{escapeStr s}\")"
  | .mdata _ e => encodeExpr ps e
  | .proj n i e => do return s!"(pr {encodeName n} {i} {← encodeExpr ps e})"

/-- Closure-node canonicalization: constructors go to their inductive; a recursor
enqueues **every** inductive of its group (mutual groups are covered whole, never
silently truncated to the first member). -/
def canonicalNames (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | some (.ctorInfo v) => [v.induct]
  | some (.recInfo v) => v.all
  | _ => [n]

/-- The canonical payload, rendered with a caller-chosen display name (the manifest
uses the real name; conformance fixtures use a placeholder to compare differently
named twins). -/
def declPayloadAs (env : Environment) (n : Name) (display : Name) :
    Except String String := do
  let some ci := env.find? n | .error s!"unknown declaration {n}"
  let ps := ci.levelParams
  let ty ← encodeExpr ps ci.type
  let head := s!"{encodeName display} {ps.length} {ty}"
  match ci with
  | .defnInfo v => do return s!"(def {head} {← encodeExpr ps v.value})"
  | .thmInfo _ => return s!"(thm {head})"
  | .axiomInfo _ => return s!"(ax {head})"
  | .opaqueInfo v => do return s!"(op {head} {← encodeExpr ps v.value})"
  | .quotInfo _ => return s!"(quot {head})"
  | .inductInfo v => do
      let ctors ← v.ctors.mapM fun c => do
        let some (.ctorInfo cv) := env.find? c | throw s!"missing constructor {c}"
        return s!"({encodeName c} {← encodeExpr cv.levelParams cv.type})"
      return s!"(ind {head} (ctors{String.join (ctors.map (" " ++ ·))}))"
  | .ctorInfo _ => .error s!"constructor {n} must be canonicalized to its inductive"
  | .recInfo _ => .error s!"recursor {n} must be canonicalized to its inductive"

def declPayload (env : Environment) (n : Name) : Except String String :=
  declPayloadAs env n n

/-- The interface dependencies: constants of the included components only — never
theorem proof bodies. Opaque values are included. -/
def interfaceDeps (env : Environment) (n : Name) : Except String (Array Name) := do
  let some ci := env.find? n | .error s!"unknown declaration {n}"
  match ci with
  | .defnInfo v => return v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => return v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => do
      let mut acc := ci.type.getUsedConstants
      for c in v.ctors do
        let some (.ctorInfo cv) := env.find? c | throw s!"missing constructor {c}"
        acc := acc ++ cv.type.getUsedConstants
      return acc
  | _ => return ci.type.getUsedConstants

/-- The recursive semantic-interface closure over `owned` declarations. -/
partial def coveredSet (env : Environment) (owned : Name → Bool) :
    List Name → NameSet → Except String NameSet
  | [], seen => .ok seen
  | n :: rest, seen => do
    match canonicalNames env n with
    | [m] =>
      if seen.contains m then coveredSet env owned rest seen
      else if !owned m then coveredSet env owned rest seen
      else do
        let deps ← interfaceDeps env m
        coveredSet env owned (deps.toList ++ rest) (seen.insert m)
    | ms => coveredSet env owned (ms ++ rest) seen

/-- The manifest: sorted (name, payload) pairs over the covered set. -/
def manifest (env : Environment) (owned : Name → Bool) (roots : List Name) :
    Except String (List (Name × String)) := do
  let seen ← coveredSet env owned roots {}
  let names := seen.toList.mergeSort (fun a b => Name.lt a b)
  names.mapM fun n => do return (n, ← declPayload env n)

/-- Exact comparison: same covered-name set, every payload equal — an under- or
over-covering manifest is rejected whole. -/
def compareManifests (a b : List (Name × String)) : Except String Unit := do
  if a.map (·.1) ≠ b.map (·.1) then
    .error "covered-name sets differ"
  for ((n, pa), (_, pb)) in a.zip b do
    if pa ≠ pb then .error s!"payload mismatch at {n}"
  return ()

end ReverseMathlib.Meta.InterfaceExpr
