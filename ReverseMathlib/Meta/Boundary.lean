/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.Commands

/-!
# Declaration-boundary checking (issue #20, first tranche)

`#rm_check_boundary thm bnd` checks that the **total** dependency closure of `thm` —
statement closure ∪ value closure, exactly `MineResult.totalClosure` — lies inside a
declared boundary `bnd : DeclBoundary`. It inspects an already-elaborated declaration;
**it is not restricted replay**. Replay (fresh compilation with approved imports, replay of
the source proof, exact statement agreement, and this boundary check) is the later runner
promised by #20; nothing here carries a `restrictedReplay` label, an evidence record, a
fragment-membership claim, a weak-system interpretation, or any RM meaning.

Why the total closure: a forbidden declaration reached through both a statement wrapper and
the proof vanishes from the proof-only difference, so a difference-based check would accept
it. Acceptance uses the total closure; statement, value, and proof-only sizes are reported
as diagnostics only. Explicit capability hypotheses are admitted **by the boundary**, never
by subtracting their dependencies.

The boundary is a coarse, revision-pinned policy, not a certified weak background:

* three explicitly distinguished allowance kinds — module **prefixes**, **exact modules**,
  and **exact declaration names** (an exact declaration admits its compiler-generated
  auxiliaries `_proof_*`, `match_*`, `eq_*`, `_f`, …, and nothing else);
* forbidden names, exact modules, and module prefixes take precedence over every allowance;
* allowances are not frontier cuts: every admitted constant is still expanded transitively,
  so a forbidden dependency beneath an allowed helper is found;
* fail closed: a truncated closure, an unknown constant (even one named in an allowance),
  a constant whose module ownership cannot be determined, or an allowed name that resolves
  to no constant all fail. The standard-axiom check is reported independently.

Documented limitation, not a test: neither ℕ-valued interfaces nor a passing declaration
audit restrict set formation, induction motives, or choice occurrences (`Classical.choice`
reaches every classical proof through `Classical.em` and decidability instances). Import
restrictions belong to the replay runner; this checker restricts declarations only.

`#rm_boundary_record thm bnd` additionally prints the canonical boundary hash and an
environment record — Lean version, mathlib revision, and the hash of the **loaded `.olean`**
of the target's module (the compiled artifact actually in the environment; hashing source
beside possibly stale object files would prove nothing).
-/

namespace ReverseMathlib.Meta

open Lean Elab Command

/-- A declaration boundary: a coarse, revision-pinned policy of what a checked
declaration's total closure may contain. -/
structure DeclBoundary where
  /-- Stable identifier, part of the canonical hash. -/
  id : String
  /-- Module prefixes admitted wholesale (`Init`, `Mathlib.Data`, …). -/
  allowedPrefixes : List Name := []
  /-- Exact modules admitted (e.g. the finite-Hall module, deliberately). -/
  allowedModules : List Name := []
  /-- Exact declarations admitted, together with their compiler-generated auxiliaries. -/
  allowedDecls : List Name := []
  /-- Forbidden module prefixes; precede every allowance. -/
  forbiddenPrefixes : List Name := []
  /-- Forbidden exact modules; precede every allowance. -/
  forbiddenModules : List Name := []
  /-- Forbidden exact declarations; precede every allowance. -/
  forbiddenDecls : List Name := []
  deriving Inhabited, Repr

namespace DeclBoundary

/-- Canonical text of a boundary: id and the six lists, each sorted. -/
def canonical (b : DeclBoundary) : String :=
  let sortNames : List Name → String := fun l =>
    ",".intercalate ((l.toArray.qsort Name.lt).toList.map toString)
  ";".intercalate [b.id, sortNames b.allowedPrefixes, sortNames b.allowedModules,
    sortNames b.allowedDecls, sortNames b.forbiddenPrefixes, sortNames b.forbiddenModules,
    sortNames b.forbiddenDecls]

/-- Hex of a 64-bit hash. -/
def hex64 (h : UInt64) : String :=
  let digits := "0123456789abcdef".toList
  let rec go (k : Nat) (v : UInt64) (acc : List Char) : List Char :=
    match k with
    | 0 => acc
    | k + 1 => go k (v / 16) (digits[(v % 16).toNat]! :: acc)
  String.ofList (go 16 h [])

/-- The canonical boundary hash (FNV-1a over the canonical text, 64-bit). -/
def hash (b : DeclBoundary) : String :=
  hex64 <| b.canonical.toUTF8.foldl (init := (14695981039346656037 : UInt64))
    fun h c => (h ^^^ c.toUInt64) * 1099511628211

end DeclBoundary

/-- Whether `n` is a compiler-generated auxiliary of `d`: `d` is a proper prefix and the
first extra component is `_…`, `match_…`, `eq_…`, or `proof_…`. -/
def isAuxiliaryOf (d n : Name) : Bool :=
  d.isPrefixOf n && d != n &&
    match (n.components.drop d.components.length) with
    | c :: _ =>
      let s := c.toString
      s.startsWith "_" || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "proof_"
    | [] => false

/-- One constant's verdict under a boundary. -/
inductive Verdict
  | forbidden (why : String)
  | admitted (how : String)
  | outside
  | unownedModule
  deriving Repr

/-- Classify one constant: forbidden rules first, then allowances, else outside. -/
def classifyConst (env : Environment) (b : DeclBoundary) (target : Name) (n : Name) :
    Verdict :=
  let mods := env.allImportedModuleNames
  match env.getModuleIdxFor? n with
  | none => .unownedModule
  | some idx =>
    let m := mods.getD idx.toNat .anonymous
    if b.forbiddenDecls.contains n then .forbidden "forbidden declaration"
    else if b.forbiddenModules.contains m then .forbidden s!"forbidden module {m}"
    else if b.forbiddenPrefixes.any (·.isPrefixOf m) then .forbidden s!"forbidden prefix of {m}"
    else if n == target || isAuxiliaryOf target n then .admitted "target"
    else if b.allowedDecls.contains n then .admitted "exact declaration"
    else if b.allowedDecls.any (isAuxiliaryOf · n) then .admitted "auxiliary of allowed"
    else if b.allowedModules.contains m then .admitted s!"exact module {m}"
    else if b.allowedPrefixes.any (·.isPrefixOf m) then .admitted s!"prefix of {m}"
    else .outside

/-- The result of a boundary check. -/
structure BoundaryReport where
  target : Name
  boundary : String
  total : Nat
  statement : Nat
  value : Nat
  proofOnly : Nat
  axioms : Array Name
  byPrefix : Nat
  byModule : Nat
  byDecl : Nat
  byAux : Nat
  offenders : Array (Name × String)

/-- Run the check. Fails closed on truncation, unknowns, unresolvable allowed names, and
unowned constants; otherwise returns the report (offenders may be nonempty). -/
def checkBoundary (target : Name) (b : DeclBoundary) : CommandElabM BoundaryReport := do
  let env ← getEnv
  for d in b.allowedDecls ++ b.forbiddenDecls do
    unless env.contains d do
      throwError "rm_check_boundary: boundary '{b.id}' names '{d}', which is not a constant \
        in this environment — a missing constant cannot be allowed or forbidden by name"
  let cfg ← mineConfig false
  let r ← match mineTarget env cfg target with
    | .ok r => pure r
    | .error e => throwError e
  requireComplete r
  unless r.unknowns.isEmpty do
    throwError "rm_check_boundary: '{target}' reaches unknown constants \
      {r.unknowns.toList} — unknowns fail closed regardless of allowances"
  let total := r.totalClosure
  let mut offenders : Array (Name × String) := #[]
  let mut byPrefix := 0
  let mut byModule := 0
  let mut byDecl := 0
  let mut byAux := 0
  for n in total.toList do
    match classifyConst env b target n with
    | .forbidden why => offenders := offenders.push (n, why)
    | .outside => offenders := offenders.push (n, "outside every allowance")
    | .unownedModule =>
      throwError "rm_check_boundary: '{n}' has no determinable module ownership (a \
        declaration of the current file?) — run the check against compiled modules"
    | .admitted how =>
      if how.startsWith "prefix" then byPrefix := byPrefix + 1
      else if how.startsWith "exact module" then byModule := byModule + 1
      else if how == "exact declaration" || how == "target" then byDecl := byDecl + 1
      else byAux := byAux + 1
  -- offenders ordered by severity of reason, then readability (public names before
  -- hygienic or private ones), then name — so the first few shown are the meaningful ones
  let severity : String → Nat := fun why =>
    if why == "forbidden declaration" then 0
    else if why.startsWith "forbidden module" then 1
    else if why.startsWith "forbidden prefix" then 2 else 3
  let ugly : Name → Bool := fun n =>
    let s := toString n
    s.startsWith "_private" || (s.splitOn "_@").length > 1 || (s.splitOn "._hyg").length > 1
  let lt : Name × String → Name × String → Bool := fun (n₁, w₁) (n₂, w₂) =>
    let (s₁, s₂) := (severity w₁, severity w₂)
    let (u₁, u₂) := ((if ugly n₁ then 1 else 0), (if ugly n₂ then 1 else 0))
    s₁ < s₂ || (s₁ == s₂ && (u₁ < u₂ || (u₁ == u₂ && Name.lt n₁ n₂)))
  return { target, boundary := b.id, total := total.size,
           statement := r.statement.reached.size, value := r.value.reached.size,
           proofOnly := r.proofOnlyClosure.size, axioms := r.axioms,
           byPrefix, byModule, byDecl, byAux,
           offenders := offenders.qsort lt }

/-- Evaluate a `DeclBoundary` constant (compiled data, evaluated by the interpreter). -/
unsafe def evalBoundaryUnsafe (id : Ident) : CommandElabM DeclBoundary := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| Lean.Meta.evalExpr DeclBoundary (Lean.mkConst ``DeclBoundary) (Lean.mkConst n)

@[implemented_by evalBoundaryUnsafe]
opaque evalBoundary (id : Ident) : CommandElabM DeclBoundary

/-- Render a passing report; facts only. -/
def BoundaryReport.summary (rep : BoundaryReport) : String :=
  "\n".intercalate
    [s!"#rm_check_boundary {rep.target} against {rep.boundary}: PASS",
     s!"  total closure: {rep.total} constants (statement {rep.statement}, value \
       {rep.value}, proof-only {rep.proofOnly}) — acceptance is on the total closure",
     s!"  admitted by: {rep.byPrefix} prefix / {rep.byModule} exact module / \
       {rep.byDecl} exact declaration / {rep.byAux} auxiliary",
     s!"  kernel axioms: {if rep.axioms.isEmpty then "(none)" else
       ", ".intercalate (rep.axioms.toList.map toString)}",
     "  a declaration audit only: no import restriction, no replay, no fragment \
       membership, no weak-system interpretation"]

/-- `#rm_check_boundary thm bnd`: fail unless every constant of `thm`'s total closure is
admitted by `bnd`. -/
elab "#rm_check_boundary " id:ident bnd:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let b ← evalBoundary bnd
  let rep ← checkBoundary target b
  unless rep.offenders.isEmpty do
    let shown := rep.offenders.toList.take 3
    let rendered := "; ".intercalate (shown.map fun (n, why) => s!"{n} ({why})")
    let more := if rep.offenders.size > 3 then s!" … and {rep.offenders.size - 3} more" else ""
    throwErrorAt id "rm_check_boundary: '{target}' leaves boundary '{b.id}': \
      {rep.offenders.size} constant(s) not admitted — {rendered}{more}"
  logInfo rep.summary

/-- FNV-1a over a byte array. -/
def hashBytes (bs : ByteArray) : String :=
  DeclBoundary.hex64 <| bs.foldl (init := (14695981039346656037 : UInt64))
    fun h c => (h ^^^ c.toUInt64) * 1099511628211

/-- `#rm_boundary_record thm bnd`: the check, plus the canonical boundary hash and the
environment record tied to the loaded compiled artifact. -/
elab "#rm_boundary_record " id:ident bnd:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let b ← evalBoundary bnd
  let rep ← checkBoundary target b
  unless rep.offenders.isEmpty do
    throwErrorAt id "rm_boundary_record: '{target}' leaves boundary '{b.id}' \
      ({rep.offenders.size} constant(s)); see #rm_check_boundary"
  let env ← getEnv
  let some idx := env.getModuleIdxFor? target
    | throwError "rm_boundary_record: '{target}' is not from a compiled module"
  let modName := env.allImportedModuleNames.getD idx.toNat .anonymous
  let olean ← findOLean modName
  let bytes ← IO.FS.readBinFile olean
  let rev? ← readMathlibRev
  logInfo <| "\n".intercalate
    [rep.summary,
     s!"  boundary hash: {b.hash} (canonical: id and the six sorted lists)",
     s!"  environment: Lean {Lean.versionString}; mathlib {rev?.getD "unavailable"}",
     s!"  loaded artifact: {modName} .olean hash {hashBytes bytes} ({bytes.size} bytes)"]

end ReverseMathlib.Meta
