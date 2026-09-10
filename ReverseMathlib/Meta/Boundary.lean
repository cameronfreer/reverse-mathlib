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
  and **exact declaration names**. Compiler-generated auxiliaries (`_proof_*`, `match_*`,
  `eq_*`, `_f`, …) of an allowed declaration — and of the target — are **not** admitted by
  their spelling, since a hand-written `foo._anything` is indistinguishable by name:
  they must be enumerated explicitly (`#rm_boundary_auxiliaries thm` lists the candidates);
* forbidden names, exact modules, and module prefixes take precedence over every allowance;
* allowances are not frontier cuts: every admitted constant is still expanded transitively,
  so a forbidden dependency beneath an allowed helper is found;
* the **root is validated too**: the target must have compiled-module ownership, must not
  be forbidden, and — if it is itself an axiom — counts as one of the closure's axioms;
* the **standard-axiom policy is enforced independently** of every allowance: the
  closure's axioms (root included) must be a subset of `propext`, `Classical.choice`,
  `Quot.sound`, whatever the boundary admits;
* fail closed: a truncated closure, an unknown constant (even one named in an allowance),
  a constant whose module ownership cannot be determined, or an allowed name that resolves
  to no constant all fail.

Documented limitation, not a test: neither ℕ-valued interfaces nor a passing declaration
audit restrict set formation, induction motives, or choice occurrences (`Classical.choice`
reaches every classical proof through `Classical.em` and decidability instances). Import
restrictions belong to the replay runner; this checker restricts declarations only.

`#rm_boundary_record thm bnd` additionally prints the canonical boundary hash and the Lean
version. **Artifact attestation is withheld**: resolving an object file on the search path
after loading does not bind the record to the loaded environment (the path can be shadowed
without changing the environment), and the manifest's mathlib revision is metadata, not
verification of the loaded dependencies. The replay runner, which compiles what it checks,
supplies that binding; this checker does not pretend to.
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
  /-- Exact declarations only; auxiliaries must be enumerated explicitly. -/
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

/-- A name that *looks like* a compiler-generated auxiliary of `d` — used only to list
candidates for explicit enumeration, never to accept anything. -/
def looksAuxiliaryOf (d n : Name) : Bool :=
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
    else if n == target then .admitted "target"
    else if b.allowedDecls.contains n then .admitted "exact declaration"
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
  offenders : Array (Name × String)
  /-- Axioms outside the standard three (root included); nonempty fails the check. -/
  nonStandardAxioms : Array Name

/-- The standard axioms every checked closure may use. -/
def boundaryStandardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Run the check. Fails closed on truncation, unknowns, unresolvable allowed names, an
unowned or forbidden root, and unowned constants; otherwise returns the report (offenders
and non-standard axioms may be nonempty). -/
def checkBoundary (target : Name) (b : DeclBoundary) : CommandElabM BoundaryReport := do
  let env ← getEnv
  -- an ALLOWED name that resolves to nothing fails closed; a FORBIDDEN name absent from
  -- the environment is trivially unreachable (the sandbox of a replay imports only the
  -- approved modules, so forbidden machinery is usually absent — that is the point)
  for d in b.allowedDecls do
    unless env.contains d do
      throwError "rm_check_boundary: boundary '{b.id}' names '{d}', which is not a constant \
        in this environment — a missing constant cannot be allowed or forbidden by name"
  -- the root itself: compiled ownership and prohibitions, checked before anything else
  match classifyConst env b target target with
  | .unownedModule =>
    throwError "rm_check_boundary: target '{target}' has no determinable module ownership \
      (a declaration of the current file?) — run the check against compiled modules"
  | .forbidden why =>
    throwError "rm_check_boundary: target '{target}' is itself forbidden by boundary \
      '{b.id}' ({why})"
  | _ => pure ()
  let rootIsAxiom := match env.find? target with
    | some (.axiomInfo _) => true
    | _ => false
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
      else byDecl := byDecl + 1
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
  let axioms := if rootIsAxiom && !r.axioms.contains target then r.axioms.push target
    else r.axioms
  let nonStandard := (axioms.filter (!boundaryStandardAxioms.contains ·)).qsort Name.lt
  return { target, boundary := b.id, total := total.size,
           statement := r.statement.reached.size, value := r.value.reached.size,
           proofOnly := r.proofOnlyClosure.size, axioms := axioms.qsort Name.lt,
           byPrefix, byModule, byDecl,
           offenders := offenders.qsort lt, nonStandardAxioms := nonStandard }

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
       {rep.byDecl} exact declaration (auxiliaries enumerated explicitly)",
     s!"  kernel axioms (root included, standard policy enforced): \
       {if rep.axioms.isEmpty then "(none)" else
        ", ".intercalate (rep.axioms.toList.map toString)}",
     "  a declaration audit only: no import restriction, no replay, no fragment \
       membership, no weak-system interpretation"]

/-- `#rm_check_boundary thm bnd`: fail unless every constant of `thm`'s total closure is
admitted by `bnd`. -/
elab "#rm_check_boundary " id:ident bnd:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let b ← evalBoundary bnd
  let rep ← checkBoundary target b
  unless rep.nonStandardAxioms.isEmpty do
    throwErrorAt id "rm_check_boundary: '{target}' depends on non-standard axiom(s) \
      {rep.nonStandardAxioms.toList} — the standard-axiom policy (propext, \
      Classical.choice, Quot.sound) is enforced independently of every allowance"
  unless rep.offenders.isEmpty do
    let shown := rep.offenders.toList.take 3
    let rendered := "; ".intercalate (shown.map fun (n, why) => s!"{n} ({why})")
    let more := if rep.offenders.size > 3 then s!" … and {rep.offenders.size - 3} more" else ""
    throwErrorAt id "rm_check_boundary: '{target}' leaves boundary '{b.id}': \
      {rep.offenders.size} constant(s) not admitted — {rendered}{more}"
  logInfo rep.summary

/-- `#rm_boundary_record thm bnd`: the check, plus the canonical boundary hash and the Lean
version. Artifact and dependency attestation are withheld — see the module doc. -/
elab "#rm_boundary_record " id:ident bnd:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let b ← evalBoundary bnd
  let rep ← checkBoundary target b
  unless rep.nonStandardAxioms.isEmpty do
    throwErrorAt id "rm_boundary_record: '{target}' depends on non-standard axiom(s) \
      {rep.nonStandardAxioms.toList}"
  unless rep.offenders.isEmpty do
    throwErrorAt id "rm_boundary_record: '{target}' leaves boundary '{b.id}' \
      ({rep.offenders.size} constant(s)); see #rm_check_boundary"
  let rev? ← readMathlibRev
  logInfo <| "\n".intercalate
    [rep.summary,
     s!"  boundary hash: {b.hash} (canonical: id and the six sorted lists)",
     s!"  Lean {Lean.versionString}; manifest mathlib revision \
       {rev?.getD "unavailable"} (metadata, not verification of the loaded dependencies)",
     "  artifact attestation: withheld — this checker inspects a loaded environment and \
       cannot bind it to an object file; the replay runner supplies that binding"]

/-- `#rm_assert_same_statement a b`: hard assertion that two declarations have **exactly**
the same statement — identical universe parameters and structurally identical types
(`Expr.equal`: binder names and binder info included; no alpha-equivalence, no defeq, no
unfolding). The replay runner uses it to tie a freshly
compiled replay to the original theorem. -/
elab "#rm_assert_same_statement " a:ident b:ident : command => do
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  let env ← getEnv
  let some ca := env.find? na | throwErrorAt a "rm_assert: unknown constant '{na}'"
  let some cb := env.find? nb | throwErrorAt b "rm_assert: unknown constant '{nb}'"
  unless ca.levelParams == cb.levelParams do
    throwErrorAt b "rm_assert: '{na}' and '{nb}' differ in universe parameters \
      ({ca.levelParams} vs {cb.levelParams})"
  -- `Expr.equal`, not `==`: structural equality that also compares binder names and
  -- binder info (`==` is alpha-equivalence and ignores explicit/implicit annotations)
  unless ca.type.equal cb.type do
    throwErrorAt b "rm_assert: statements of '{na}' and '{nb}' are not structurally \
      identical (binder names and binder info included):\n  {ca.type}\n  {cb.type}"
  logInfo s!"#rm_assert_same_statement: '{na}' and '{nb}' have structurally identical \
    statements ({ca.levelParams.length} universe parameter(s))"

/-- `#rm_assert_owned_by decl Mod`: hard assertion that `decl` is a constant of the compiled
module `Mod` in the loaded environment (not of the current file, not of any other module). -/
elab "#rm_assert_owned_by " id:ident m:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let mods := env.allImportedModuleNames
  match env.getModuleIdxFor? n with
  | none => throwErrorAt id "rm_assert: '{n}' is not owned by any compiled module"
  | some idx =>
    let owner := mods.getD idx.toNat .anonymous
    unless owner == m.getId do
      throwErrorAt m "rm_assert: '{n}' is owned by module '{owner}', not '{m.getId}'"
    logInfo s!"#rm_assert_owned_by: '{n}' is owned by compiled module '{owner}'"

/-- `#rm_assert_module_imports Mod [A, B, …]`: hard assertion that the **compiled** module
`Mod` loaded in this environment records exactly the direct imports `A, B, …` (as the
`.olean` states them — what the module was actually compiled against), in any order. -/
elab "#rm_assert_module_imports " m:ident "[" mods:ident,* "]" : command => do
  let env ← getEnv
  let names := env.allImportedModuleNames
  let some idx := names.findIdx? (· == m.getId)
    | throwErrorAt m "rm_assert: module '{m.getId}' is not loaded"
  let some data := env.header.moduleData[idx]?
    | throwErrorAt m "rm_assert: no module data for '{m.getId}'"
  -- every module implicitly imports the prelude `Init`; it is not part of the contract
  let actual := ((data.imports.map (·.module)).filter (· != `Init)).qsort Name.lt
  let expected := ((mods.getElems.map (·.getId)).filter (· != `Init)).qsort Name.lt
  unless actual == expected do
    throwErrorAt m "rm_assert: compiled module '{m.getId}' records direct imports \
      {actual.toList}, not the expected {expected.toList}"
  logInfo s!"#rm_assert_module_imports: '{m.getId}' was compiled with exactly \
    {actual.toList}"

/-- `#rm_boundary_auxiliaries thm`: list the constants of `thm`'s total closure whose names
look like compiler-generated auxiliaries of `thm` or of any constant in the closure — the
candidates an author enumerates explicitly in a boundary. Listing only; admits nothing. -/
elab "#rm_boundary_auxiliaries " id:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let cfg ← mineConfig false
  let r ← match mineTarget env cfg target with
    | .ok r => pure r
    | .error e => throwError e
  requireComplete r
  let total := r.totalClosure
  let mods := env.allImportedModuleNames
  let owned : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => (`ReverseMathlib).isPrefixOf (mods.getD idx.toNat .anonymous)
    | none => false
  let names := total.toList
  let cands := names.filter fun n =>
    owned n && (looksAuxiliaryOf target n || names.any fun d => d != n && looksAuxiliaryOf d n)
  let sorted := cands.toArray.qsort Name.lt
  logInfo s!"#rm_boundary_auxiliaries {target}: {sorted.size} candidate(s) — \
    {sorted.toList}"

end ReverseMathlib.Meta
